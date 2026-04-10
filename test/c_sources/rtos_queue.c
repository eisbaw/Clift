/* rtos_queue.c -- Realistic RTOS blocking queue with priority
 *
 * Faithfully represents FreeRTOS queue patterns:
 * - Fixed-size circular buffer (no malloc in hot path)
 * - Priority-based insertion
 * - ISR-safe push/pop variants (simplified: no actual interrupt disable,
 *   but structured as if there were critical sections)
 * - Error codes for all failure paths
 *
 * Constraints (CImporter subset):
 *   - No arrays (use slot structs instead)
 *   - No floating point, goto, longjmp, VLAs
 *   - No pointer-to-pointer
 *   - No malloc/free
 *   - No side effects in expressions
 */

#include <stdint.h>
#include <stddef.h>

/* ================================================================
 * Data structures
 * ================================================================ */

/* A single queue item with priority and payload */
struct queue_item {
    uint32_t data;
    uint32_t priority;       /* 0 = lowest, higher = more urgent */
    uint32_t sequence;       /* Insertion order for FIFO within same priority */
    struct queue_item *next;
};

/* Queue state: linked list ordered by priority (descending) then sequence (ascending) */
struct queue_state {
    struct queue_item *head;       /* Highest priority item (dequeue from here) */
    struct queue_item *tail;       /* Lowest priority item */
    uint32_t count;                /* Current number of items */
    uint32_t capacity;             /* Maximum items allowed */
    uint32_t next_sequence;        /* Monotonically increasing sequence counter */
    uint32_t lock_count;           /* Simulated critical section nesting depth */
};

/* Wait queue: tasks blocked on this queue */
struct wait_entry {
    uint32_t task_id;
    uint32_t timeout_ticks;
    struct wait_entry *next;
};

struct wait_queue {
    struct wait_entry *head;
    uint32_t count;
};

/* Error codes */
#define Q_OK            0
#define Q_ERR_FULL      1
#define Q_ERR_EMPTY     2
#define Q_ERR_INVAL     3
#define Q_ERR_TIMEOUT   4
#define Q_ERR_ISR       5

/* ================================================================
 * Initialization
 * ================================================================ */

/* Initialize a queue with the given capacity. */
uint32_t queue_init(struct queue_state *q, uint32_t cap) {
    if (cap == 0) {
        return Q_ERR_INVAL;
    }
    q->head = NULL;
    q->tail = NULL;
    q->count = 0;
    q->capacity = cap;
    q->next_sequence = 0;
    q->lock_count = 0;
    return Q_OK;
}

/* Initialize a wait queue. */
void wait_queue_init(struct wait_queue *wq) {
    wq->head = NULL;
    wq->count = 0;
}

/* ================================================================
 * Lock simulation (critical section enter/exit)
 * ================================================================ */

/* Enter critical section (increment lock nesting). */
uint32_t queue_lock(struct queue_state *q) {
    q->lock_count = q->lock_count + 1;
    return Q_OK;
}

/* Exit critical section (decrement lock nesting). Returns error if not locked. */
uint32_t queue_unlock(struct queue_state *q) {
    if (q->lock_count == 0) {
        return Q_ERR_INVAL;
    }
    q->lock_count = q->lock_count - 1;
    return Q_OK;
}

/* Check if queue is in a critical section. */
uint32_t queue_is_locked(struct queue_state *q) {
    if (q->lock_count > 0) {
        return 1;
    }
    return 0;
}

/* ================================================================
 * Core operations
 * ================================================================ */

/* Push an item into the queue, maintaining priority order.
 * Higher priority items go toward the head.
 * Items with the same priority maintain FIFO order (by sequence number). */
uint32_t queue_push(struct queue_state *q, struct queue_item *item,
                    uint32_t data, uint32_t priority) {
    struct queue_item *cur;
    struct queue_item *prev;

    if (q->count >= q->capacity) {
        return Q_ERR_FULL;
    }

    item->data = data;
    item->priority = priority;
    item->sequence = q->next_sequence;
    q->next_sequence = q->next_sequence + 1;
    item->next = NULL;

    /* Empty queue: item becomes both head and tail */
    if (q->head == NULL) {
        q->head = item;
        q->tail = item;
        q->count = q->count + 1;
        return Q_OK;
    }

    /* Insert at head if highest priority */
    if (priority > q->head->priority) {
        item->next = q->head;
        q->head = item;
        q->count = q->count + 1;
        return Q_OK;
    }

    /* Walk to find insertion point: after all items with >= priority */
    prev = q->head;
    cur = q->head->next;
    while (cur != NULL) {
        if (priority > cur->priority) {
            /* Insert before cur (after prev) */
            prev->next = item;
            item->next = cur;
            q->count = q->count + 1;
            return Q_OK;
        }
        prev = cur;
        cur = cur->next;
    }

    /* Lowest priority: append at tail */
    prev->next = item;
    q->tail = item;
    q->count = q->count + 1;
    return Q_OK;
}

/* Pop the highest-priority item from the queue.
 * Returns data in *out_data, priority in *out_priority. */
uint32_t queue_pop(struct queue_state *q, uint32_t *out_data,
                   uint32_t *out_priority) {
    struct queue_item *front;
    if (q->head == NULL) {
        return Q_ERR_EMPTY;
    }
    front = q->head;
    *out_data = front->data;
    *out_priority = front->priority;
    q->head = front->next;
    if (q->head == NULL) {
        q->tail = NULL;
    }
    front->next = NULL;
    q->count = q->count - 1;
    return Q_OK;
}

/* Peek at the highest-priority item without removing it. */
uint32_t queue_peek(struct queue_state *q, uint32_t *out_data,
                    uint32_t *out_priority) {
    if (q->head == NULL) {
        return Q_ERR_EMPTY;
    }
    *out_data = q->head->data;
    *out_priority = q->head->priority;
    return Q_OK;
}

/* ================================================================
 * ISR-safe variants (simplified: check lock_count instead of interrupt state)
 * ================================================================ */

/* ISR-safe push: only allowed from within a critical section. */
uint32_t queue_push_from_isr(struct queue_state *q, struct queue_item *item,
                             uint32_t data, uint32_t priority) {
    if (q->lock_count == 0) {
        return Q_ERR_ISR;
    }
    return queue_push(q, item, data, priority);
}

/* ISR-safe pop: only allowed from within a critical section. */
uint32_t queue_pop_from_isr(struct queue_state *q, uint32_t *out_data,
                            uint32_t *out_priority) {
    if (q->lock_count == 0) {
        return Q_ERR_ISR;
    }
    return queue_pop(q, out_data, out_priority);
}

/* ================================================================
 * Query operations
 * ================================================================ */

/* Get current item count. */
uint32_t queue_count(struct queue_state *q) {
    return q->count;
}

/* Check if queue is empty. */
uint32_t queue_is_empty(struct queue_state *q) {
    if (q->count == 0) {
        return 1;
    }
    return 0;
}

/* Check if queue is full. */
uint32_t queue_is_full(struct queue_state *q) {
    if (q->count >= q->capacity) {
        return 1;
    }
    return 0;
}

/* Get remaining capacity. */
uint32_t queue_remaining(struct queue_state *q) {
    return q->capacity - q->count;
}

/* ================================================================
 * Traversal and search
 * ================================================================ */

/* Check if queue contains an item with the given data value. */
uint32_t queue_contains(struct queue_state *q, uint32_t data) {
    struct queue_item *cur;
    cur = q->head;
    while (cur != NULL) {
        if (cur->data == data) {
            return 1;
        }
        cur = cur->next;
    }
    return 0;
}

/* Count items with a specific priority level. */
uint32_t queue_count_priority(struct queue_state *q, uint32_t priority) {
    struct queue_item *cur;
    uint32_t n;
    n = 0;
    cur = q->head;
    while (cur != NULL) {
        if (cur->priority == priority) {
            n = n + 1;
        }
        cur = cur->next;
    }
    return n;
}

/* Get the highest priority value in the queue. Returns 0 if empty. */
uint32_t queue_highest_priority(struct queue_state *q) {
    if (q->head == NULL) {
        return 0;
    }
    return q->head->priority;
}

/* ================================================================
 * Maintenance operations
 * ================================================================ */

/* Clear all items. Returns number of items removed. */
uint32_t queue_clear(struct queue_state *q) {
    struct queue_item *cur;
    struct queue_item *nxt;
    uint32_t removed;
    removed = 0;
    cur = q->head;
    while (cur != NULL) {
        nxt = cur->next;
        cur->next = NULL;
        cur = nxt;
        removed = removed + 1;
    }
    q->head = NULL;
    q->tail = NULL;
    q->count = 0;
    return removed;
}

/* Check structural integrity: traverse and verify count matches. */
uint32_t queue_check_integrity(struct queue_state *q) {
    struct queue_item *cur;
    uint32_t actual;
    uint32_t prev_priority;
    actual = 0;
    cur = q->head;
    if (cur != NULL) {
        prev_priority = cur->priority;
    } else {
        prev_priority = 0;
    }
    while (cur != NULL) {
        /* Priority must be non-increasing (head has highest priority) */
        if (cur->priority > prev_priority) {
            return 0;
        }
        prev_priority = cur->priority;
        actual = actual + 1;
        cur = cur->next;
    }
    if (actual != q->count) {
        return 0;
    }
    /* Empty queue invariant */
    if (q->count == 0) {
        if (q->head != NULL) {
            return 0;
        }
        if (q->tail != NULL) {
            return 0;
        }
    }
    /* Non-empty queue invariant */
    if (q->count != 0) {
        if (q->head == NULL) {
            return 0;
        }
        if (q->tail == NULL) {
            return 0;
        }
    }
    return 1;
}

/* ================================================================
 * Wait queue operations
 * ================================================================ */

/* Add a task to the wait queue. */
uint32_t wait_queue_add(struct wait_queue *wq, struct wait_entry *entry,
                        uint32_t task_id, uint32_t timeout) {
    entry->task_id = task_id;
    entry->timeout_ticks = timeout;
    entry->next = wq->head;
    wq->head = entry;
    wq->count = wq->count + 1;
    return Q_OK;
}

/* Remove the first entry from the wait queue (wake up one task).
 * Returns the task_id in *out_task_id. */
uint32_t wait_queue_wake_one(struct wait_queue *wq, uint32_t *out_task_id) {
    struct wait_entry *front;
    if (wq->head == NULL) {
        return Q_ERR_EMPTY;
    }
    front = wq->head;
    *out_task_id = front->task_id;
    wq->head = front->next;
    front->next = NULL;
    wq->count = wq->count - 1;
    return Q_OK;
}

/* Count waiting tasks. */
uint32_t wait_queue_count(struct wait_queue *wq) {
    return wq->count;
}

/* Check if any tasks are waiting. */
uint32_t wait_queue_is_empty(struct wait_queue *wq) {
    if (wq->count == 0) {
        return 1;
    }
    return 0;
}

/* Decrement all timeout ticks. Returns number of entries that hit zero. */
uint32_t wait_queue_tick(struct wait_queue *wq) {
    struct wait_entry *cur;
    uint32_t expired;
    expired = 0;
    cur = wq->head;
    while (cur != NULL) {
        if (cur->timeout_ticks > 0) {
            cur->timeout_ticks = cur->timeout_ticks - 1;
            if (cur->timeout_ticks == 0) {
                expired = expired + 1;
            }
        }
        cur = cur->next;
    }
    return expired;
}
