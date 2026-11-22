package com.markel.flowstate.core.data

import android.content.Context
import android.content.SharedPreferences
import android.security.keystore.KeyGenParameterSpec
import android.security.keystore.KeyProperties
import android.util.Base64
import com.markel.flowstate.core.data.local.CategoryDao
import com.markel.flowstate.core.data.local.CategoryEntity
import com.markel.flowstate.core.data.local.HabitDao
import com.markel.flowstate.core.data.local.HabitEntity
import com.markel.flowstate.core.data.local.HabitEntryEntity
import com.markel.flowstate.core.data.local.HabitNumericEntryEntity
import com.markel.flowstate.core.data.local.TaskDao
import com.markel.flowstate.core.data.local.TaskEntity
import com.markel.flowstate.core.domain.Category
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlinx.coroutines.withContext
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonArray
import kotlinx.serialization.json.JsonElement
import kotlinx.serialization.json.JsonNull
import kotlinx.serialization.json.JsonObject
import kotlinx.serialization.json.JsonPrimitive
import kotlinx.serialization.json.buildJsonObject
import kotlinx.serialization.json.contentOrNull
import kotlinx.serialization.json.intOrNull
import kotlinx.serialization.json.jsonArray
import kotlinx.serialization.json.jsonObject
import kotlinx.serialization.json.jsonPrimitive
import java.io.IOException
import java.net.HttpURLConnection
import java.net.URL
import java.nio.charset.StandardCharsets
import java.security.KeyStore
import java.security.MessageDigest
import java.time.DayOfWeek
import java.time.Instant
import java.time.LocalDate
import java.time.OffsetDateTime
import java.time.ZoneOffset
import javax.crypto.Cipher
import javax.crypto.KeyGenerator
import javax.crypto.SecretKey
import javax.crypto.spec.GCMParameterSpec
import javax.inject.Inject
import javax.inject.Singleton
import dagger.hilt.android.qualifiers.ApplicationContext

/** Result returned to the Android Cloud Sync settings panel. */
data class CloudSyncSummary(
    val tasks: Int,
    val habits: Int,
    val habitEntries: Int,
    val categories: Int
) {
    fun asMessage(): String = "Sync complete: $tasks tasks, $habits habits, $habitEntries habit entries and $categories categories processed."
}

/**
 * Supabase email authentication and bidirectional synchronisation for FlowState's
 * Room tasks, categories, habits and habit entries.
 *
 * The existing Room database remains the offline source of truth. The server's
 * local_id columns are used to keep this installation's integer Room IDs stable.
 * The sync stamp stores the last common fingerprint and server update time so a
 * remote dashboard edit can be pulled, while a local-only edit can be uploaded.
 */
@Singleton
class FlowStateCloudSyncRepository @Inject constructor(
    @ApplicationContext private val context: Context,
    private val taskDao: TaskDao,
    private val categoryDao: CategoryDao,
    private val habitDao: HabitDao
) {
    companion object {
        private const val SUPABASE_URL = "https://lulszgrxepeeltibwqlo.supabase.co"
        private const val SUPABASE_PUBLISHABLE_KEY = "sb_publishable_oaISnnd_Xp4eJ2YRhy25qw_Ub9_ybe1"
        private const val PREFS_NAME = "flowstate_cloud_sync"
        private const val SESSION_KEY = "encrypted_session"
        private const val STAMPS_KEY = "sync_stamps"
        private const val KEY_ALIAS = "flowstate_cloud_session_key"
    }

    private val prefs: SharedPreferences = context.getSharedPreferences(PREFS_NAME, Context.MODE_PRIVATE)
    private val syncMutex = Mutex()

    private data class Session(
        val accessToken: String,
        val refreshToken: String,
        val expiresAt: Long,
        val userId: String,
        val email: String
    )

    private data class Stamp(
        val remoteId: String,
        val snapshot: String,
        val remoteUpdatedAt: Long
    )

    fun currentEmail(): String? = readSession()?.email
    fun isSignedIn(): Boolean = readSession() != null

    suspend fun signIn(email: String, password: String) {
        require(email.isNotBlank()) { "Enter your email address." }
        require(password.length >= 8) { "Password must contain at least 8 characters." }
        val response = request(
            method = "POST",
            path = "/auth/v1/token?grant_type=password",
            body = buildJsonObject {
                put("email", email.trim())
                put("password", password)
            },
            authenticated = false
        ).jsonObject
        val user = response["user"]?.jsonObject ?: error("Supabase did not return a user profile.")
        val session = Session(
            accessToken = response.string("access_token") ?: error("Missing access token."),
            refreshToken = response.string("refresh_token") ?: error("Missing refresh token."),
            expiresAt = System.currentTimeMillis() + ((response.long("expires_in") ?: 3600L) * 1000L),
            userId = user.string("id") ?: error("Missing user ID."),
            email = user.string("email") ?: email.trim()
        )
        writeSession(session)
    }

    suspend fun signOut() {
        val session = readSession()
        if (session != null) {
            runCatching { request("POST", "/auth/v1/logout", null, token = session.accessToken) }
        }
        prefs.edit().remove(SESSION_KEY).apply()
    }

    suspend fun syncNow(): CloudSyncSummary = syncMutex.withLock {
        val session = validSession()
        val stamps = readStamps()
        val categoryMap = syncCategories(session, stamps)
        val habitMap = syncHabits(session, stamps)
        val taskCount = syncTasks(session, stamps, categoryMap)
        val entryCount = syncHabitEntries(session, stamps, habitMap)
        writeStamps(stamps)
        CloudSyncSummary(
            tasks = taskCount,
            habits = habitMap.size,
            habitEntries = entryCount,
            categories = categoryMap.size
        )
    }

    // ── Categories ──────────────────────────────────────────────────────────

    private suspend fun syncCategories(
        session: Session,
        stamps: MutableMap<String, Stamp>
    ): Map<Int, String> {
        val remote = getRows(session, "fs_categories")
        val local = categoryDao.getAllCategoriesOnce()
        val remoteByLocal = remote.mapNotNull { row -> row.int("local_id")?.let { it to row } }.toMap()
        val localToRemote = mutableMapOf<Int, String>()
        val remoteToLocal = mutableMapOf<String, Int>()

        for (category in local) {
            val key = "category:${category.id}"
            val found = remoteByLocal[category.id]
            val row = if (found == null) {
                upsertRow(session, "fs_categories", "user_id,local_id", categoryPayload(session, category))
            } else {
                val stamp = stamps[key]
                val localHash = categoryHash(category)
                val remoteHash = categoryHash(found)
                val updated = found.long("updated_at_ms") ?: isoMillis(found.string("updated_at"))
                val localChanged = stamp != null && stamp.snapshot != localHash
                val remoteChanged = stamp != null && updated > stamp.remoteUpdatedAt
                when {
                    stamp == null && remoteHash != localHash -> upsertRow(session, "fs_categories", "user_id,local_id", categoryPayload(session, category))
                    localChanged -> upsertRow(session, "fs_categories", "user_id,local_id", categoryPayload(session, category))
                    remoteChanged -> {
                        categoryDao.upsertCategory(category.copy(
                            name = found.string("name") ?: category.name,
                            position = found.int("position") ?: category.position
                        ))
                        found
                    }
                    else -> found
                }
            }
            val remoteId = row.string("id") ?: continue
            val updated = isoMillis(row.string("updated_at"))
            val hash = categoryHash(categoryDao.getCategoryById(category.id) ?: category)
            stamps[key] = Stamp(remoteId, hash, updated)
            localToRemote[category.id] = remoteId
            remoteToLocal[remoteId] = category.id
        }

        // Import categories created in the dashboard that do not yet have a Room ID.
        for (row in remote) {
            if (row.string("deleted_at") != null || row.int("local_id") != null) continue
            val remoteId = row.string("id") ?: continue
            val insertedId = categoryDao.upsertCategory(
                CategoryEntity(name = row.string("name") ?: "Category", position = row.int("position") ?: 0)
            ).toInt()
            val linked = JsonObject(row.toMutableMap() + ("local_id" to JsonPrimitive(insertedId)))
            val updatedRow = upsertRow(session, "fs_categories", "id", linked)
            val key = "category:$insertedId"
            stamps[key] = Stamp(remoteId, categoryHash(categoryDao.getCategoryById(insertedId)!!), isoMillis(updatedRow.string("updated_at")))
            localToRemote[insertedId] = remoteId
            remoteToLocal[remoteId] = insertedId
        }
        return localToRemote
    }

    private fun categoryPayload(session: Session, category: CategoryEntity): JsonObject = buildJsonObject {
        put("user_id", session.userId)
        put("local_id", category.id)
        put("name", category.name)
        put("position", category.position)
        put("updated_at", Instant.now().toString())
    }

    private fun categoryHash(category: CategoryEntity): String = sha256("${category.name}|${category.position}")
    private fun categoryHash(row: JsonObject): String = sha256("${row.string("name") ?: ""}|${row.int("position") ?: 0}")

    // ── Tasks ────────────────────────────────────────────────────────────────

    private suspend fun syncTasks(
        session: Session,
        stamps: MutableMap<String, Stamp>,
        categoryMap: Map<Int, String>
    ): Int {
        val remote = getRows(session, "fs_tasks")
        val remoteByLocal = remote.mapNotNull { row -> row.int("local_id")?.let { it to row } }.toMap()
        val localTasks = taskDao.getAllTasksOnce().map { it.task }
        val remoteCategoryToLocal = categoryMap.entries.associate { it.value to it.key }
        var processed = 0

        for (task in localTasks) {
            val key = "task:${task.id}"
            val existing = remoteByLocal[task.id]
            if (existing?.string("deleted_at") != null) {
                taskDao.getTaskById(task.id)?.let { taskDao.deleteTaskEntity(it.task) }
                stamps.remove(key)
                continue
            }
            val localHash = taskHash(task)
            val row = if (existing == null) {
                upsertRow(session, "fs_tasks", "user_id,local_id", taskPayload(session, task, categoryMap[task.categoryId]))
            } else {
                val stamp = stamps[key]
                val remoteUpdated = isoMillis(existing.string("updated_at"))
                val localChanged = stamp != null && stamp.snapshot != localHash
                val remoteChanged = stamp != null && remoteUpdated > stamp.remoteUpdatedAt
                when {
                    stamp == null && taskHash(existing, remoteCategoryToLocal) != localHash ->
                        upsertRow(session, "fs_tasks", "user_id,local_id", taskPayload(session, task, categoryMap[task.categoryId], existing))
                    localChanged ->
                        upsertRow(session, "fs_tasks", "user_id,local_id", taskPayload(session, task, categoryMap[task.categoryId], existing))
                    remoteChanged -> {
                        val updated = taskFromRemote(existing, task.id, remoteCategoryToLocal)
                        taskDao.upsertTaskEntity(updated)
                        existing
                    }
                    else -> existing
                }
            }
            val remoteId = row.string("id") ?: continue
            val current = taskDao.getTaskById(task.id)?.task ?: task
            stamps[key] = Stamp(remoteId, taskHash(current), isoMillis(row.string("updated_at")))
            processed++
        }

        // Pull tasks created on the web dashboard (local_id is NULL).
        for (row in remote) {
            if (row.string("deleted_at") != null || row.int("local_id") != null) continue
            val remoteId = row.string("id") ?: continue
            val entity = taskFromRemote(row, 0, remoteCategoryToLocal)
            val localId = taskDao.upsertTaskEntity(entity).toInt()
            val linked = JsonObject(row.toMutableMap() + ("local_id" to JsonPrimitive(localId)))
            val result = upsertRow(session, "fs_tasks", "id", linked)
            val current = taskDao.getTaskById(localId)?.task ?: entity.copy(id = localId)
            stamps["task:$localId"] = Stamp(remoteId, taskHash(current), isoMillis(result.string("updated_at")))
            processed++
        }

        // A cloud-side soft delete is reflected locally. Local deletes are kept local
        // for this first release; the next sync revision will add delete tombstones.
        for (row in remote) {
            if (row.string("deleted_at") == null) continue
            val localId = row.int("local_id") ?: continue
            taskDao.getTaskById(localId)?.let { taskDao.deleteTaskEntity(it.task) }
            stamps.remove("task:$localId")
        }
        return processed
    }

    private fun taskPayload(
        session: Session,
        task: TaskEntity,
        remoteCategoryId: String?,
        existing: JsonObject? = null
    ): JsonObject = buildJsonObject {
        put("user_id", session.userId)
        put("local_id", task.id)
        put("title", task.title)
        put("description", task.description)
        put("is_done", task.isDone)
        put("position", task.position)
        put("priority", priorityName(task.priority))
        putNullable("due_date", task.dueDate?.let(::toIso))
        putNullable("completed_at", task.completedAt?.let(::toIso))
        putNullable("reminder_time", task.reminderTime?.let(::toIso))
        putNullable("category_id", remoteCategoryId)
        // FlowState 3.5.4 has due-date/reminder fields, not native time-block fields.
        // Preserve web-created schedule metadata when updating an existing row.
        putNullable("scheduled_start", existing?.string("scheduled_start"))
        putNullable("scheduled_end", existing?.string("scheduled_end"))
        putNullable("recurrence_rule", existing?.string("recurrence_rule"))
        put("updated_at", Instant.now().toString())
        put("deleted_at", JsonNull)
    }

    private fun taskFromRemote(row: JsonObject, localId: Int, categoryToLocal: Map<String, Int>): TaskEntity {
        val categoryUuid = row.string("category_id")
        return TaskEntity(
            id = localId,
            title = row.string("title") ?: "Untitled task",
            description = row.string("description") ?: "",
            isDone = row.boolean("is_done") ?: false,
            position = row.int("position") ?: 0,
            priority = priorityIndex(row.string("priority")),
            dueDate = isoMillisOrNull(row.string("due_date")),
            completedAt = isoMillisOrNull(row.string("completed_at")),
            reminderTime = isoMillisOrNull(row.string("reminder_time")),
            categoryId = categoryUuid?.let { categoryToLocal[it] } ?: Category.GENERAL_ID
        )
    }

    private fun taskHash(task: TaskEntity): String = sha256(
        listOf(task.title, task.description, task.isDone, task.position, task.priority,
            task.dueDate, task.completedAt, task.reminderTime, task.categoryId).joinToString("|")
    )

    private fun taskHash(row: JsonObject, categoryToLocal: Map<String, Int>): String = sha256(
        listOf(row.string("title") ?: "", row.string("description") ?: "", row.boolean("is_done") ?: false,
            row.int("position") ?: 0, priorityIndex(row.string("priority")),
            isoMillisOrNull(row.string("due_date")), isoMillisOrNull(row.string("completed_at")),
            isoMillisOrNull(row.string("reminder_time")), row.string("category_id")?.let { categoryToLocal[it] } ?: Category.GENERAL_ID
        ).joinToString("|")
    )

    // ── Habits and habit entries ────────────────────────────────────────────

    private suspend fun syncHabits(session: Session, stamps: MutableMap<String, Stamp>): Map<Int, String> {
        val remote = getRows(session, "fs_habits")
        val remoteByLocal = remote.mapNotNull { row -> row.int("local_id")?.let { it to row } }.toMap()
        val localHabits = habitDao.getAllHabitsOnce().map { it.habit }
        val localToRemote = mutableMapOf<Int, String>()

        for (habit in localHabits) {
            val key = "habit:${habit.id}"
            val existing = remoteByLocal[habit.id]
            if (existing?.string("deleted_at") != null) {
                habitDao.getHabitById(habit.id)?.let { habitDao.deleteHabit(it) }
                stamps.remove(key)
                continue
            }
            val localHash = habitHash(habit)
            val row = if (existing == null) {
                upsertRow(session, "fs_habits", "user_id,local_id", habitPayload(session, habit))
            } else {
                val stamp = stamps[key]
                val remoteUpdated = isoMillis(existing.string("updated_at"))
                val localChanged = stamp != null && stamp.snapshot != localHash
                val remoteChanged = stamp != null && remoteUpdated > stamp.remoteUpdatedAt
                when {
                    stamp == null && habitHash(existing) != localHash -> upsertRow(session, "fs_habits", "user_id,local_id", habitPayload(session, habit, existing))
                    localChanged -> upsertRow(session, "fs_habits", "user_id,local_id", habitPayload(session, habit, existing))
                    remoteChanged -> {
                        habitDao.updateHabit(habitFromRemote(existing, habit.id))
                        existing
                    }
                    else -> existing
                }
            }
            val remoteId = row.string("id") ?: continue
            val current = habitDao.getHabitById(habit.id) ?: habit
            stamps[key] = Stamp(remoteId, habitHash(current), isoMillis(row.string("updated_at")))
            localToRemote[habit.id] = remoteId
        }

        // Import habits created from the dashboard.
        for (row in remote) {
            if (row.string("deleted_at") != null || row.int("local_id") != null) continue
            val remoteId = row.string("id") ?: continue
            val id = habitDao.insertHabit(habitFromRemote(row, 0)).toInt()
            val linked = JsonObject(row.toMutableMap() + ("local_id" to JsonPrimitive(id)))
            val updated = upsertRow(session, "fs_habits", "id", linked)
            val current = habitDao.getHabitById(id) ?: habitFromRemote(row, id)
            stamps["habit:$id"] = Stamp(remoteId, habitHash(current), isoMillis(updated.string("updated_at")))
            localToRemote[id] = remoteId
        }

        // Reflect cloud-side habit deletion locally.
        for (row in remote) {
            if (row.string("deleted_at") == null) continue
            val id = row.int("local_id") ?: continue
            habitDao.getHabitById(id)?.let { habitDao.deleteHabit(it) }
            stamps.remove("habit:$id")
        }
        return localToRemote
    }

    private fun habitPayload(session: Session, habit: HabitEntity, existing: JsonObject? = null): JsonObject = buildJsonObject {
        put("user_id", session.userId)
        put("local_id", habit.id)
        put("name", habit.name)
        put("icon_name", habit.iconName)
        put("color_argb", habit.colorArgb.toLong())
        put("created_on", LocalDate.ofInstant(Instant.ofEpochMilli(habit.createdAt), ZoneOffset.UTC).toString())
        put("habit_type", habit.habitType)
        putNullable("unit", habit.unit)
        putNullable("target_value", habit.targetValue?.toDouble())
        put("step", habit.step.toDouble())
        put("position", habit.position)
        put("scheduled_days", JsonArray(habit.scheduledDays.sortedBy { it.value }.map { JsonPrimitive(it.value) }))
        put("updated_at", Instant.now().toString())
        put("deleted_at", JsonNull)
    }

    private fun habitFromRemote(row: JsonObject, localId: Int): HabitEntity {
        val days = row["scheduled_days"]?.let { element ->
            runCatching { element.jsonArray.mapNotNull { it.jsonPrimitive.intOrNull }.map { DayOfWeek.of(it) }.toSet() }.getOrNull()
        }?.takeIf { it.isNotEmpty() } ?: DayOfWeek.entries.toSet()
        val createdOn = row.string("created_on")?.let { runCatching { LocalDate.parse(it).atStartOfDay(ZoneOffset.UTC).toInstant().toEpochMilli() }.getOrNull() }
        return HabitEntity(
            id = localId,
            name = row.string("name") ?: "Habit",
            iconName = row.string("icon_name") ?: "self_improvement",
            colorArgb = row.long("color_argb")?.toInt() ?: 0xFF6650A4.toInt(),
            createdAt = createdOn ?: System.currentTimeMillis(),
            habitType = row.string("habit_type") ?: "BOOLEAN",
            unit = row.string("unit"),
            targetValue = row.double("target_value")?.toFloat(),
            step = row.double("step")?.toFloat() ?: 1f,
            position = row.int("position") ?: 0,
            scheduledDays = days
        )
    }

    private fun habitHash(h: HabitEntity): String = sha256(
        listOf(h.name, h.iconName, h.colorArgb, h.habitType, h.unit, h.targetValue, h.step,
            h.position, h.scheduledDays.sortedBy { it.value }.joinToString(",") { it.value.toString() }
        ).joinToString("|")
    )

    private fun habitHash(row: JsonObject): String = sha256(
        listOf(row.string("name") ?: "", row.string("icon_name") ?: "self_improvement",
            row.long("color_argb")?.toInt() ?: 0xFF6650A4.toInt(), row.string("habit_type") ?: "BOOLEAN",
            row.string("unit"), row.double("target_value"), row.double("step") ?: 1.0,
            row.int("position") ?: 0,
            row["scheduled_days"]?.jsonArray?.joinToString(",") { it.jsonPrimitive.content } ?: "1,2,3,4,5,6,7"
        ).joinToString("|")
    )

    private suspend fun syncHabitEntries(
        session: Session,
        stamps: MutableMap<String, Stamp>,
        habits: Map<Int, String>
    ): Int {
        val remote = getRows(session, "fs_habit_entries")
        val remoteHabitsToLocal = habits.entries.associate { it.value to it.key }
        val remoteByNaturalKey = remote.mapNotNull { row ->
            val h = row.string("habit_id") ?: return@mapNotNull null
            val date = row.string("entry_date") ?: return@mapNotNull null
            "$h|$date" to row
        }.toMap()
        val localBoolean = habitDao.getAllEntriesOnce()
        val localNumeric = habitDao.getAllNumericEntriesOnce()
        val localValues = mutableMapOf<String, Pair<Int, Float>>()
        localBoolean.forEach { localValues["${it.habitId}:${it.completedAt}"] = it.habitId to 1f }
        localNumeric.forEach { localValues["${it.habitId}:${it.epochDay}"] = it.habitId to it.value }
        var processed = 0

        for ((localKey, pair) in localValues) {
            val (habitId, value) = pair
            val remoteHabitId = habits[habitId] ?: continue
            val epochDay = localKey.substringAfter(':').toLongOrNull() ?: continue
            val date = LocalDate.ofEpochDay(epochDay).toString()
            val naturalKey = "$remoteHabitId|$date"
            val existing = remoteByNaturalKey[naturalKey]
            val stampKey = "entry:$localKey"
            if (existing?.string("deleted_at") != null) {
                val habit = habitDao.getHabitById(habitId)
                if (habit?.habitType == "NUMERIC") habitDao.deleteNumericEntry(habitId, epochDay)
                else habitDao.deleteEntry(habitId, epochDay)
                stamps.remove(stampKey)
                continue
            }
            val localHash = sha256(value.toString())
            val row = if (existing == null) {
                upsertRow(session, "fs_habit_entries", "user_id,habit_id,entry_date", habitEntryPayload(session, remoteHabitId, date, value))
            } else {
                val stamp = stamps[stampKey]
                val remoteUpdated = isoMillis(existing.string("updated_at"))
                val remoteHash = sha256((existing.double("value") ?: 1.0).toString())
                val localChanged = stamp != null && stamp.snapshot != localHash
                val remoteChanged = stamp != null && remoteUpdated > stamp.remoteUpdatedAt
                when {
                    stamp == null && remoteHash != localHash -> upsertRow(session, "fs_habit_entries", "user_id,habit_id,entry_date", habitEntryPayload(session, remoteHabitId, date, value, existing))
                    localChanged -> upsertRow(session, "fs_habit_entries", "user_id,habit_id,entry_date", habitEntryPayload(session, remoteHabitId, date, value, existing))
                    remoteChanged -> {
                        applyRemoteEntry(habitId, epochDay, existing.double("value")?.toFloat() ?: 1f)
                        existing
                    }
                    else -> existing
                }
            }
            val remoteId = row.string("id") ?: existing?.string("id") ?: continue
            val actualValue = localValue(habitId, epochDay) ?: value
            stamps[stampKey] = Stamp(remoteId, sha256(actualValue.toString()), isoMillis(row.string("updated_at")))
            processed++
        }

        // Pull habit progress created or changed on the web dashboard.
        for (row in remote) {
            val remoteHabitId = row.string("habit_id") ?: continue
            val localHabitId = remoteHabitsToLocal[remoteHabitId] ?: continue
            val dateText = row.string("entry_date") ?: continue
            val epochDay = runCatching { LocalDate.parse(dateText).toEpochDay() }.getOrNull() ?: continue
            val key = "${localHabitId}:${epochDay}"
            val stampKey = "entry:$key"
            val value = (row.double("value") ?: 1.0).toFloat()
            if (row.string("deleted_at") == null && stamps[stampKey] != null && !localValues.containsKey(key)) {
                // A previously-synced entry removed on this phone is soft-deleted in the cloud.
                val tombstone = JsonObject(row.toMutableMap() + mapOf(
                    "deleted_at" to JsonPrimitive(Instant.now().toString()),
                    "updated_at" to JsonPrimitive(Instant.now().toString())
                ))
                upsertRow(session, "fs_habit_entries", "user_id,habit_id,entry_date", tombstone)
                stamps.remove(stampKey)
                continue
            }
            if (row.string("deleted_at") != null) {
                val habit = habitDao.getHabitById(localHabitId)
                if (habit?.habitType == "NUMERIC") habitDao.deleteNumericEntry(localHabitId, epochDay)
                else habitDao.deleteEntry(localHabitId, epochDay)
                stamps.remove(stampKey)
                continue
            }
            val hasLocal = localValues.containsKey(key)
            if (!hasLocal) {
                applyRemoteEntry(localHabitId, epochDay, value)
            }
            val localValue = localValue(localHabitId, epochDay) ?: value
            stamps[stampKey] = Stamp(row.string("id") ?: "", sha256(localValue.toString()), isoMillis(row.string("updated_at")))
            processed++
        }
        return processed
    }

    private fun habitEntryPayload(
        session: Session,
        remoteHabitId: String,
        date: String,
        value: Float,
        existing: JsonObject? = null
    ): JsonObject = buildJsonObject {
        put("user_id", session.userId)
        existing?.string("id")?.let { put("id", it) }
        put("habit_id", remoteHabitId)
        put("entry_date", date)
        put("value", value.toDouble())
        putNullable("completed_at", if (value > 0f) "${date}T12:00:00Z" else null)
        put("updated_at", Instant.now().toString())
        put("deleted_at", JsonNull)
    }

    private suspend fun applyRemoteEntry(habitId: Int, epochDay: Long, value: Float) {
        val habit = habitDao.getHabitById(habitId) ?: return
        if (habit.habitType == "NUMERIC") {
            habitDao.upsertNumericEntry(HabitNumericEntryEntity(habitId = habitId, epochDay = epochDay, value = value))
        } else if (value > 0f && habitDao.getEntry(habitId, epochDay) == null) {
            habitDao.insertEntry(HabitEntryEntity(habitId = habitId, completedAt = epochDay))
        } else if (value <= 0f) {
            habitDao.deleteEntry(habitId, epochDay)
        }
    }

    private suspend fun localValue(habitId: Int, epochDay: Long): Float? {
        val habit = habitDao.getHabitById(habitId) ?: return null
        return if (habit.habitType == "NUMERIC") {
            habitDao.getAllNumericEntriesOnce().firstOrNull { it.habitId == habitId && it.epochDay == epochDay }?.value
        } else {
            if (habitDao.getEntry(habitId, epochDay) != null) 1f else null
        }
    }

    // ── REST/auth helpers ────────────────────────────────────────────────────

    private suspend fun validSession(): Session {
        val session = readSession() ?: error("Sign in to FlowState Cloud first.")
        if (session.expiresAt > System.currentTimeMillis() + 60_000L) return session
        val refreshed = request(
            method = "POST",
            path = "/auth/v1/token?grant_type=refresh_token",
            body = buildJsonObject { put("refresh_token", session.refreshToken) },
            authenticated = false
        ).jsonObject
        val user = refreshed["user"]?.jsonObject
        val next = Session(
            accessToken = refreshed.string("access_token") ?: error("Session refresh failed."),
            refreshToken = refreshed.string("refresh_token") ?: session.refreshToken,
            expiresAt = System.currentTimeMillis() + ((refreshed.long("expires_in") ?: 3600L) * 1000L),
            userId = user?.string("id") ?: session.userId,
            email = user?.string("email") ?: session.email
        )
        writeSession(next)
        return next
    }

    private suspend fun getRows(session: Session, table: String): List<JsonObject> {
        val response = request("GET", "/rest/v1/$table?select=*", token = session.accessToken)
        return response.jsonArray.map { it.jsonObject }
    }

    private suspend fun upsertRow(
        session: Session,
        table: String,
        conflict: String,
        body: JsonObject
    ): JsonObject {
        val result = request(
            method = "POST",
            path = "/rest/v1/$table?on_conflict=$conflict",
            body = JsonArray(listOf(body)),
            token = session.accessToken,
            prefer = "resolution=merge-duplicates,return=representation"
        )
        return result.jsonArray.firstOrNull()?.jsonObject ?: error("Supabase did not return the saved $table record.")
    }

    private suspend fun request(
        method: String,
        path: String,
        body: JsonElement? = null,
        token: String? = null,
        authenticated: Boolean = true,
        prefer: String? = null
    ): JsonElement = withContext(Dispatchers.IO) {
        val connection = (URL(SUPABASE_URL + path).openConnection() as HttpURLConnection).apply {
            requestMethod = method
            connectTimeout = 20_000
            readTimeout = 30_000
            setRequestProperty("apikey", SUPABASE_PUBLISHABLE_KEY)
            setRequestProperty("Accept", "application/json")
            if (authenticated && token != null) setRequestProperty("Authorization", "Bearer $token")
            if (prefer != null) setRequestProperty("Prefer", prefer)
            if (body != null) {
                doOutput = true
                setRequestProperty("Content-Type", "application/json; charset=utf-8")
                outputStream.use { it.write(body.toString().toByteArray(StandardCharsets.UTF_8)) }
            }
        }
        try {
            val status = connection.responseCode
            val stream = if (status in 200..299) connection.inputStream else connection.errorStream
            val responseText = stream?.bufferedReader(StandardCharsets.UTF_8)?.use { it.readText() }.orEmpty()
            if (status !in 200..299) {
                val message = runCatching { Json.parseToJsonElement(responseText).jsonObject.string("message") }.getOrNull()
                    ?: responseText.take(400).ifBlank { "HTTP $status" }
                throw IOException(message)
            }
            if (responseText.isBlank()) JsonArray(emptyList()) else Json.parseToJsonElement(responseText)
        } finally {
            connection.disconnect()
        }
    }

    // ── Encrypted local session and lightweight sync stamps ────────────────

    private fun readSession(): Session? = runCatching {
        val encrypted = prefs.getString(SESSION_KEY, null) ?: return null
        val payload = decrypt(encrypted).jsonObject
        Session(
            accessToken = payload.string("access_token") ?: return null,
            refreshToken = payload.string("refresh_token") ?: return null,
            expiresAt = payload.long("expires_at") ?: return null,
            userId = payload.string("user_id") ?: return null,
            email = payload.string("email") ?: return null
        )
    }.getOrNull()

    private fun writeSession(session: Session) {
        val payload = buildJsonObject {
            put("access_token", session.accessToken)
            put("refresh_token", session.refreshToken)
            put("expires_at", session.expiresAt)
            put("user_id", session.userId)
            put("email", session.email)
        }.toString()
        prefs.edit().putString(SESSION_KEY, encrypt(payload)).apply()
    }

    private fun readStamps(): MutableMap<String, Stamp> = runCatching {
        val raw = prefs.getString(STAMPS_KEY, "{}") ?: "{}"
        Json.parseToJsonElement(raw).jsonObject.mapValues { (_, v) ->
            val row = v.jsonObject
            Stamp(
                remoteId = row.string("remote_id") ?: "",
                snapshot = row.string("snapshot") ?: "",
                remoteUpdatedAt = row.long("remote_updated_at") ?: 0L
            )
        }.toMutableMap()
    }.getOrDefault(mutableMapOf())

    private fun writeStamps(stamps: Map<String, Stamp>) {
        val value = buildJsonObject {
            stamps.forEach { (key, stamp) ->
                put(key, buildJsonObject {
                    put("remote_id", stamp.remoteId)
                    put("snapshot", stamp.snapshot)
                    put("remote_updated_at", stamp.remoteUpdatedAt)
                })
            }
        }
        prefs.edit().putString(STAMPS_KEY, value.toString()).apply()
    }

    private fun encrypt(plain: String): String {
        val key = getOrCreateKey()
        val cipher = Cipher.getInstance("AES/GCM/NoPadding")
        cipher.init(Cipher.ENCRYPT_MODE, key)
        val encrypted = cipher.doFinal(plain.toByteArray(StandardCharsets.UTF_8))
        return Base64.encodeToString(cipher.iv + encrypted, Base64.NO_WRAP)
    }

    private fun decrypt(encoded: String): JsonElement {
        val bytes = Base64.decode(encoded, Base64.NO_WRAP)
        val iv = bytes.copyOfRange(0, 12)
        val ciphertext = bytes.copyOfRange(12, bytes.size)
        val cipher = Cipher.getInstance("AES/GCM/NoPadding")
        cipher.init(Cipher.DECRYPT_MODE, getOrCreateKey(), GCMParameterSpec(128, iv))
        return Json.parseToJsonElement(String(cipher.doFinal(ciphertext), StandardCharsets.UTF_8))
    }

    private fun getOrCreateKey(): SecretKey {
        val store = KeyStore.getInstance("AndroidKeyStore").apply { load(null) }
        (store.getKey(KEY_ALIAS, null) as? SecretKey)?.let { return it }
        val generator = KeyGenerator.getInstance(KeyProperties.KEY_ALGORITHM_AES, "AndroidKeyStore")
        generator.init(
            KeyGenParameterSpec.Builder(KEY_ALIAS, KeyProperties.PURPOSE_ENCRYPT or KeyProperties.PURPOSE_DECRYPT)
                .setBlockModes(KeyProperties.BLOCK_MODE_GCM)
                .setEncryptionPaddings(KeyProperties.ENCRYPTION_PADDING_NONE)
                .setRandomizedEncryptionRequired(true)
                .build()
        )
        return generator.generateKey()
    }

    // ── Conversion helpers ──────────────────────────────────────────────────

    private fun isoMillis(value: String?): Long = isoMillisOrNull(value) ?: 0L
    private fun isoMillisOrNull(value: String?): Long? = value?.let {
        runCatching { OffsetDateTime.parse(it).toInstant().toEpochMilli() }
            .recoverCatching { Instant.parse(it).toEpochMilli() }
            .getOrNull()
    }
    private fun toIso(millis: Long): String = Instant.ofEpochMilli(millis).toString()
    private fun priorityName(value: Int): String = listOf("NOTHING", "LOW", "MEDIUM", "HIGH").getOrElse(value) { "NOTHING" }
    private fun priorityIndex(value: String?): Int = listOf("NOTHING", "LOW", "MEDIUM", "HIGH").indexOf(value).let { if (it < 0) 0 else it }
    private fun sha256(value: String): String = MessageDigest.getInstance("SHA-256")
        .digest(value.toByteArray(StandardCharsets.UTF_8)).joinToString("") { "%02x".format(it) }

    private fun JsonObject.string(key: String): String? = this[key]?.let {
        if (it == JsonNull) null else runCatching { it.jsonPrimitive.contentOrNull }.getOrNull()
    }
    private fun JsonObject.int(key: String): Int? = this[key]?.let { runCatching { it.jsonPrimitive.intOrNull }.getOrNull() }
    private fun JsonObject.long(key: String): Long? = this[key]?.let { runCatching { it.jsonPrimitive.content.toLong() }.getOrNull() }
    private fun JsonObject.double(key: String): Double? = this[key]?.let { runCatching { it.jsonPrimitive.content.toDouble() }.getOrNull() }
    private fun JsonObject.boolean(key: String): Boolean? = this[key]?.let { runCatching { it.jsonPrimitive.content.toBooleanStrict() }.getOrNull() }

    private fun kotlinx.serialization.json.JsonObjectBuilder.putNullable(key: String, value: String?) {
        put(key, value?.let(::JsonPrimitive) ?: JsonNull)
    }
    private fun kotlinx.serialization.json.JsonObjectBuilder.putNullable(key: String, value: Double?) {
        put(key, value?.let(::JsonPrimitive) ?: JsonNull)
    }
}
