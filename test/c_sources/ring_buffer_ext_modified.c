/* ring_buffer_ext.c -- Extended ring buffer for seL4-scale test
 *
 * This extends ring_buffer.c with additional operations to reach ~500 LOC.
 * Exercises: struct pointers, linked list traversal, state invariants,
 *            multiple interacting functions, heap read/write, conditionals,
 *            loops, error handling patterns, multi-struct interaction.
 *
 * DESIGN: Same constraints as ring_buffer.c:
 *   - No arrays (CImporter limitation)
 *   - No pointer-to-pointer
 *   - No malloc/free (external allocator)
 *   - No floating point, goto, longjmp, VLAs
 *
 * Additional structures: rb_stats (statistics tracking),
 *                        rb_iter (iterator for traversal)
 *
 * Functions (30):
 *   Core (from ring_buffer.c):
 *     rb_init, rb_push, rb_pop, rb_peek, rb_size, rb_is_empty, rb_is_full,
 *     rb_clear, rb_count_nodes, rb_contains, rb_peek_back,
 *     rb_check_integrity, rb_increment_all, rb_sum, rb_capacity, rb_remaining
 *   Extended:
 *     rb_push_if_not_full, rb_pop_if_not_empty, rb_drain_to,
 *     rb_find_index, rb_nth, rb_remove_first_match,
 *     rb_stats_init, rb_stats_update, rb_stats_reset,
 *     rb_iter_init, rb_iter_next, rb_iter_has_next,
 *     rb_copy_to, rb_equal,
 *     rb_swap_front_back
 */

#include <stdint.h>
#include <stddef.h>

/* ================================================================
 * Data structures
 * ================================================================ */

/* Node in the ring buffer's internal linked list */
struct rb_node {
    uint32_t value;
    struct rb_node *next;
};

/* Ring buffer state */
struct rb_state {
    struct rb_node *head;    /* Front of queue (dequeue from here) */
    struct rb_node *tail;    /* Back of queue (enqueue here) */
    uint32_t count;          /* Number of elements currently in buffer */
    uint32_t capacity;       /* Maximum number of elements */
    uint32_t version;        /* CHANGE 1: added version counter for CAS-style updates */
};

/* Statistics tracker for a ring buffer */
struct rb_stats {
    uint32_t total_pushes;    /* Lifetime push count */
    uint32_t total_pops;      /* Lifetime pop count */
    uint32_t push_failures;   /* Push attempts when full */
    uint32_t pop_failures;    /* Pop attempts when empty */
    uint32_t peak_usage;      /* High water mark for count */
};

/* Iterator for traversing a ring buffer without modification */
struct rb_iter {
    struct rb_node *current;  /* Current position in traversal */
    uint32_t remaining;       /* Elements remaining to visit */
};

/* ================================================================
 * Core operations (same as ring_buffer.c)
 * ================================================================ */

/* Initialize a ring buffer state. */
uint32_t rb_init(struct rb_state *rb, uint32_t cap) {
    if (cap == 0) {
        return 1;
    }
    rb->head = NULL;
    rb->tail = NULL;
    rb->count = 0;
    rb->capacity = cap;
    return 0;
}

/* Push a value into the ring buffer. */
uint32_t rb_push(struct rb_state *rb, struct rb_node *node, uint32_t val) {
    if (rb->count >= rb->capacity) {
        return 1;
    }
    node->value = val;
    node->next = NULL;
    if (rb->tail != NULL) {
        rb->tail->next = node;
    }
    rb->tail = node;
    if (rb->head == NULL) {
        rb->head = node;
    }
    rb->count = rb->count + 1;
    return 0;
}

/* Pop a value from the front. */
uint32_t rb_pop(struct rb_state *rb, uint32_t *out_val) {
    struct rb_node *front;
    if (rb->head == NULL) {
        return 1;
    }
    front = rb->head;
    *out_val = front->value;
    rb->head = front->next;
    if (rb->head == NULL) {
        rb->tail = NULL;
    }
    rb->count = rb->count - 1;
    front->next = NULL;
    return 0;
}

/* Peek at the front value without removing it. */
uint32_t rb_peek(struct rb_state *rb, uint32_t *out_val) {
    if (rb->head == NULL) {
        return 1;
    }
    *out_val = rb->head->value;
    return 0;
}

/* Return element count. */
uint32_t rb_size(struct rb_state *rb) {
    return rb->count;
}

/* Return 1 if empty. */
uint32_t rb_is_empty(struct rb_state *rb) {
    if (rb->count == 0) {
        return 1;
    }
    return 0;
}

/* Return 1 if full. */
uint32_t rb_is_full(struct rb_state *rb) {
    if (rb->count >= rb->capacity) {
        return 1;
    }
    return 0;
}

/* Clear all elements. Returns count of removed nodes. */
uint32_t rb_clear(struct rb_state *rb) {
    struct rb_node *cur;
    struct rb_node *nxt;
    uint32_t removed;
    removed = 0;
    cur = rb->head;
    while (cur != NULL) {
        nxt = cur->next;
        cur->next = NULL;
        cur = nxt;
        removed = removed + 1;
    }
    rb->head = NULL;
    rb->tail = NULL;
    rb->count = 0;
    return removed;
}

/* Count nodes by traversal. */
uint32_t rb_count_nodes(struct rb_state *rb) {
    struct rb_node *cur;
    uint32_t n;
    n = 0;
    cur = rb->head;
    while (cur != NULL) {
        n = n + 1;
        cur = cur->next;
    }
    return n;
}

/* CHANGE 2: rb_contains now does early-exit if buffer is empty (algorithm change). */
uint32_t rb_contains(struct rb_state *rb, uint32_t val) {
    struct rb_node *cur;
    uint32_t checked;
    if (rb->count == 0) {
        return 0;
    }
    checked = 0;
    cur = rb->head;
    while (cur != NULL) {
        if (cur->value == val) {
            return 1;
        }
        checked = checked + 1;
        if (checked >= rb->count) {
            return 0;
        }
        cur = cur->next;
    }
    return 0;
}

/* Peek at the back (tail) value. */
uint32_t rb_peek_back(struct rb_state *rb, uint32_t *out_val) {
    if (rb->tail == NULL) {
        return 1;
    }
    *out_val = rb->tail->value;
    return 0;
}

/* Check structural integrity. */
uint32_t rb_check_integrity(struct rb_state *rb) {
    uint32_t actual;
    actual = rb_count_nodes(rb);
    if (actual != rb->count) {
        return 0;
    }
    if (rb->count == 0) {
        if (rb->head != NULL) {
            return 0;
        }
        if (rb->tail != NULL) {
            return 0;
        }
    }
    if (rb->count != 0) {
        if (rb->head == NULL) {
            return 0;
        }
        if (rb->tail == NULL) {
            return 0;
        }
    }
    return 1;
}

/* Increment all values by delta. */
uint32_t rb_increment_all(struct rb_state *rb, uint32_t delta) {
    struct rb_node *cur;
    uint32_t modified;
    modified = 0;
    cur = rb->head;
    while (cur != NULL) {
        cur->value = cur->value + delta;
        modified = modified + 1;
        cur = cur->next;
    }
    return modified;
}

/* Sum all values. */
uint32_t rb_sum(struct rb_state *rb) {
    struct rb_node *cur;
    uint32_t total;
    total = 0;
    cur = rb->head;
    while (cur != NULL) {
        total = total + cur->value;
        cur = cur->next;
    }
    return total;
}

/* Get capacity. */
uint32_t rb_capacity(struct rb_state *rb) {
    return rb->capacity;
}

/* Get remaining space. */
uint32_t rb_remaining(struct rb_state *rb) {
    return rb->capacity - rb->count;
}

/* ================================================================
 * Extended operations
 * ================================================================ */

/* Push only if buffer is not full. Returns the value pushed (for chaining),
 * or 0xFFFFFFFF on failure. This is a convenience wrapper. */
uint32_t rb_push_if_not_full(struct rb_state *rb, struct rb_node *node, uint32_t val) {
    uint32_t result;
    if (rb->count >= rb->capacity) {
        return 0xFFFFFFFF;
    }
    result = rb_push(rb, node, val);
    if (result != 0) {
        return 0xFFFFFFFF;
    }
    return val;
}

/* Pop only if buffer is not empty. Stores value in *out_val.
 * Returns 0 on success, 1 on failure. */
uint32_t rb_pop_if_not_empty(struct rb_state *rb, uint32_t *out_val) {
    uint32_t result;
    if (rb->count == 0) {
        return 1;
    }
    result = rb_pop(rb, out_val);
    return result;
}

/* Drain up to max_drain elements from src into dst.
 * Each popped node from src is pushed into dst.
 * Uses scratch pointer for intermediate value transfer.
 * Returns the number of elements actually transferred. */
uint32_t rb_drain_to(struct rb_state *src, struct rb_state *dst,
                     struct rb_node *temp_node, uint32_t *scratch,
                     uint32_t max_drain) {
    uint32_t transferred;
    uint32_t pop_result;
    uint32_t push_result;
    transferred = 0;
    while (transferred < max_drain) {
        if (src->count == 0) {
            return transferred;
        }
        if (dst->count >= dst->capacity) {
            return transferred;
        }
        pop_result = rb_pop(src, scratch);
        if (pop_result != 0) {
            return transferred;
        }
        push_result = rb_push(dst, temp_node, *scratch);
        if (push_result != 0) {
            return transferred;
        }
        transferred = transferred + 1;
    }
    return transferred;
}

/* Find the 0-based index of the first occurrence of val.
 * Returns the index, or 0xFFFFFFFF if not found. */
uint32_t rb_find_index(struct rb_state *rb, uint32_t val) {
    struct rb_node *cur;
    uint32_t idx;
    idx = 0;
    cur = rb->head;
    while (cur != NULL) {
        if (cur->value == val) {
            return idx;
        }
        idx = idx + 1;
        cur = cur->next;
    }
    return 0xFFFFFFFF;
}

/* Get the value at 0-based index n.
 * Stores value in *out_val. Returns 0 on success, 1 if index out of range. */
uint32_t rb_nth(struct rb_state *rb, uint32_t n, uint32_t *out_val) {
    struct rb_node *cur;
    uint32_t idx;
    if (n >= rb->count) {
        return 1;
    }
    idx = 0;
    cur = rb->head;
    while (cur != NULL) {
        if (idx == n) {
            *out_val = cur->value;
            return 0;
        }
        idx = idx + 1;
        cur = cur->next;
    }
    return 1;
}

/* Remove the first node whose value matches val.
 * The removed node's next is set to NULL.
 * Returns 0 on success, 1 if not found. */
uint32_t rb_remove_first_match(struct rb_state *rb, uint32_t val) {
    struct rb_node *cur;
    struct rb_node *prev;
    if (rb->head == NULL) {
        return 1;
    }
    /* Check head node */
    if (rb->head->value == val) {
        cur = rb->head;
        rb->head = cur->next;
        if (rb->head == NULL) {
            rb->tail = NULL;
        }
        cur->next = NULL;
        rb->count = rb->count - 1;
        return 0;
    }
    /* Walk the rest */
    prev = rb->head;
    cur = rb->head->next;
    while (cur != NULL) {
        if (cur->value == val) {
            prev->next = cur->next;
            if (cur == rb->tail) {
                rb->tail = prev;
            }
            cur->next = NULL;
            rb->count = rb->count - 1;
            return 0;
        }
        prev = cur;
        cur = cur->next;
    }
    return 1;
}

/* ================================================================
 * Statistics operations
 * ================================================================ */

/* Initialize statistics tracker. */
void rb_stats_init(struct rb_stats *stats) {
    stats->total_pushes = 0;
    stats->total_pops = 0;
    stats->push_failures = 0;
    stats->pop_failures = 0;
    stats->peak_usage = 0;
}

/* Update statistics after a push attempt.
 * push_ok: 0 = success, nonzero = failure
 * current_count: current element count after the push attempt */
void rb_stats_update_push(struct rb_stats *stats, uint32_t push_ok,
                          uint32_t current_count) {
    if (push_ok == 0) {
        stats->total_pushes = stats->total_pushes + 1;
        if (current_count > stats->peak_usage) {
            stats->peak_usage = current_count;
        }
    } else {
        stats->push_failures = stats->push_failures + 1;
    }
}

/* Update statistics after a pop attempt.
 * pop_ok: 0 = success, nonzero = failure */
void rb_stats_update_pop(struct rb_stats *stats, uint32_t pop_ok) {
    if (pop_ok == 0) {
        stats->total_pops = stats->total_pops + 1;
    } else {
        stats->pop_failures = stats->pop_failures + 1;
    }
}

/* Reset statistics to zero. */
void rb_stats_reset(struct rb_stats *stats) {
    stats->total_pushes = 0;
    stats->total_pops = 0;
    stats->push_failures = 0;
    stats->pop_failures = 0;
    stats->peak_usage = 0;
}

/* Get the total operations count (pushes + pops + failures). */
uint32_t rb_stats_total_ops(struct rb_stats *stats) {
    return stats->total_pushes + stats->total_pops +
           stats->push_failures + stats->pop_failures;
}

/* ================================================================
 * Iterator operations
 * ================================================================ */

/* Initialize an iterator at the front of the buffer. */
void rb_iter_init(struct rb_iter *iter, struct rb_state *rb) {
    iter->current = rb->head;
    iter->remaining = rb->count;
}

/* Check if iterator has more elements. Returns 1 if yes. */
uint32_t rb_iter_has_next(struct rb_iter *iter) {
    if (iter->current != NULL) {
        return 1;
    }
    return 0;
}

/* Advance iterator and store current value in *out_val.
 * Returns 0 on success, 1 if no more elements. */
uint32_t rb_iter_next(struct rb_iter *iter, uint32_t *out_val) {
    if (iter->current == NULL) {
        return 1;
    }
    *out_val = iter->current->value;
    iter->current = iter->current->next;
    if (iter->remaining > 0) {
        iter->remaining = iter->remaining - 1;
    }
    return 0;
}

/* Skip n elements in the iterator. Returns number actually skipped. */
uint32_t rb_iter_skip(struct rb_iter *iter, uint32_t n) {
    uint32_t skipped;
    skipped = 0;
    while (skipped < n) {
        if (iter->current == NULL) {
            return skipped;
        }
        iter->current = iter->current->next;
        if (iter->remaining > 0) {
            iter->remaining = iter->remaining - 1;
        }
        skipped = skipped + 1;
    }
    return skipped;
}

/* ================================================================
 * Multi-buffer operations
 * ================================================================ */

/* Check if two buffers have the same content (by traversal).
 * Returns 1 if equal (same length and same values), 0 otherwise. */
uint32_t rb_equal(struct rb_state *a, struct rb_state *b) {
    struct rb_node *ca;
    struct rb_node *cb;
    if (a->count != b->count) {
        return 0;
    }
    ca = a->head;
    cb = b->head;
    while (ca != NULL) {
        if (cb == NULL) {
            return 0;
        }
        if (ca->value != cb->value) {
            return 0;
        }
        ca = ca->next;
        cb = cb->next;
    }
    if (cb != NULL) {
        return 0;
    }
    return 1;
}

/* Swap the front and back values of the buffer (if it has >= 2 elements).
 * Returns 0 on success, 1 if fewer than 2 elements. */
uint32_t rb_swap_front_back(struct rb_state *rb) {
    uint32_t tmp;
    if (rb->count < 2) {
        return 1;
    }
    if (rb->head == NULL) {
        return 1;
    }
    if (rb->tail == NULL) {
        return 1;
    }
    tmp = rb->head->value;
    rb->head->value = rb->tail->value;
    rb->tail->value = tmp;
    return 0;
}

/* Compute the minimum value in the buffer.
 * Stores result in *out_val. Returns 0 on success, 1 if empty. */
uint32_t rb_min(struct rb_state *rb, uint32_t *out_val) {
    struct rb_node *cur;
    uint32_t min_val;
    if (rb->head == NULL) {
        return 1;
    }
    min_val = rb->head->value;
    cur = rb->head->next;
    while (cur != NULL) {
        if (cur->value < min_val) {
            min_val = cur->value;
        }
        cur = cur->next;
    }
    *out_val = min_val;
    return 0;
}

/* Compute the maximum value in the buffer.
 * Stores result in *out_val. Returns 0 on success, 1 if empty. */
uint32_t rb_max(struct rb_state *rb, uint32_t *out_val) {
    struct rb_node *cur;
    uint32_t max_val;
    if (rb->head == NULL) {
        return 1;
    }
    max_val = rb->head->value;
    cur = rb->head->next;
    while (cur != NULL) {
        if (cur->value > max_val) {
            max_val = cur->value;
        }
        cur = cur->next;
    }
    *out_val = max_val;
    return 0;
}

/* Replace all occurrences of old_val with new_val.
 * Returns the number of replacements made. */
uint32_t rb_replace_all(struct rb_state *rb, uint32_t old_val, uint32_t new_val) {
    struct rb_node *cur;
    uint32_t replaced;
    replaced = 0;
    cur = rb->head;
    while (cur != NULL) {
        if (cur->value == old_val) {
            cur->value = new_val;
            replaced = replaced + 1;
        }
        cur = cur->next;
    }
    return replaced;
}

/* Reverse the linked list in the buffer. Head becomes tail and vice versa.
 * Returns 0 on success, 1 if empty or single element (no-op). */
uint32_t rb_reverse(struct rb_state *rb) {
    struct rb_node *prev;
    struct rb_node *cur;
    struct rb_node *nxt;
    struct rb_node *old_head;
    if (rb->count < 2) {
        return 1;
    }
    old_head = rb->head;
    prev = NULL;
    cur = rb->head;
    while (cur != NULL) {
        nxt = cur->next;
        cur->next = prev;
        prev = cur;
        cur = nxt;
    }
    rb->head = prev;
    rb->tail = old_head;
    return 0;
}

/* Count how many elements satisfy predicate val > threshold.
 * Returns the count. */
uint32_t rb_count_above(struct rb_state *rb, uint32_t threshold) {
    struct rb_node *cur;
    uint32_t count;
    count = 0;
    cur = rb->head;
    while (cur != NULL) {
        if (cur->value > threshold) {
            count = count + 1;
        }
        cur = cur->next;
    }
    return count;
}

/* Count how many elements satisfy predicate val <= threshold. */
uint32_t rb_count_at_or_below(struct rb_state *rb, uint32_t threshold) {
    struct rb_node *cur;
    uint32_t count;
    count = 0;
    cur = rb->head;
    while (cur != NULL) {
        if (cur->value <= threshold) {
            count = count + 1;
        }
        cur = cur->next;
    }
    return count;
}

/* Set all values to a constant. Returns the number of nodes updated. */
uint32_t rb_fill(struct rb_state *rb, uint32_t val) {
    struct rb_node *cur;
    uint32_t filled;
    filled = 0;
    cur = rb->head;
    while (cur != NULL) {
        cur->value = val;
        filled = filled + 1;
        cur = cur->next;
    }
    return filled;
}

/* CHANGE 3: New function -- compute running average (integer division). */
uint32_t rb_average(struct rb_state *rb) {
    struct rb_node *cur;
    uint32_t total;
    if (rb->count == 0) {
        return 0;
    }
    total = 0;
    cur = rb->head;
    while (cur != NULL) {
        total = total + cur->value;
        cur = cur->next;
    }
    return total / rb->count;
}
