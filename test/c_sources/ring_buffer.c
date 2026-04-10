/* ring_buffer.c -- Ring buffer / circular queue implementation
 *
 * This module implements a ring buffer using a singly-linked list of nodes
 * rather than an array, because the CImporter does not yet support array
 * subscript operations. The linked-list approach exercises the same
 * verification challenges: struct pointers, traversal, state invariants,
 * and multiple interacting functions.
 *
 * Functions (15): rb_init, rb_push, rb_pop, rb_peek, rb_size, rb_is_empty,
 *                 rb_is_full, rb_clear, rb_count_nodes, rb_find, rb_contains,
 *                 rb_peek_back, rb_check_integrity, rb_increment_all, rb_sum
 *
 * Invariants:
 *   - count <= capacity
 *   - count == 0 iff head == NULL iff tail == NULL
 *   - count == number of nodes in the linked list from head to tail
 *   - tail->next == NULL (not circular; "ring" in name refers to FIFO semantics)
 *
 * Memory model: We assume an external allocator provides nodes. The ring buffer
 * does not call malloc/free (those are not in our CImporter's scope). Instead,
 * push takes a node pointer from the caller. Pop detaches the head and
 * writes the value to an output pointer.
 *
 * DESIGN NOTE: We avoid pointer-to-pointer (e.g. struct rb_node **) because
 * the CImporter flattens nested pointer types. All output values go through
 * scalar pointers (uint32_t *) or struct field updates.
 */

#include <stdint.h>
#include <stddef.h>

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
};

/* Initialize a ring buffer state.
 * Sets head and tail to NULL, count to 0, capacity to cap.
 * Returns 0 on success, 1 if cap is 0. */
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

/* Push a value into the ring buffer.
 * The caller provides a pre-allocated node.
 * Returns 0 on success, 1 if buffer is full. */
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

/* Pop a value from the front of the ring buffer.
 * Stores the value in *out_val. The head node is detached.
 * Returns 0 on success, 1 if empty. */
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

/* Peek at the front value without removing it.
 * Stores the value in *out_val. Returns 0 on success, 1 if empty. */
uint32_t rb_peek(struct rb_state *rb, uint32_t *out_val) {
    if (rb->head == NULL) {
        return 1;
    }
    *out_val = rb->head->value;
    return 0;
}

/* Return the number of elements in the buffer. */
uint32_t rb_size(struct rb_state *rb) {
    return rb->count;
}

/* Return 1 if buffer is empty, 0 otherwise. */
uint32_t rb_is_empty(struct rb_state *rb) {
    if (rb->count == 0) {
        return 1;
    }
    return 0;
}

/* Return 1 if buffer is full, 0 otherwise. */
uint32_t rb_is_full(struct rb_state *rb) {
    if (rb->count >= rb->capacity) {
        return 1;
    }
    return 0;
}

/* Clear the buffer by walking the list and detaching all nodes.
 * Each detached node's next pointer is set to NULL.
 * After clearing, the buffer is empty.
 * Returns the count of nodes that were removed. */
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

/* Count elements by traversal (for verification: compare with rb->count).
 * This provides an independent check that the linked list length matches count. */
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

/* Check if the buffer contains a value. Returns 1 if yes, 0 if no. */
uint32_t rb_contains(struct rb_state *rb, uint32_t val) {
    struct rb_node *cur;
    cur = rb->head;
    while (cur != NULL) {
        if (cur->value == val) {
            return 1;
        }
        cur = cur->next;
    }
    return 0;
}

/* Get the tail (last enqueued) value. Returns 0 on success, 1 if empty. */
uint32_t rb_peek_back(struct rb_state *rb, uint32_t *out_val) {
    if (rb->tail == NULL) {
        return 1;
    }
    *out_val = rb->tail->value;
    return 0;
}

/* Check structural integrity: count matches actual list length.
 * Returns 1 if valid, 0 if inconsistent. */
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

/* Apply a transformation: increment all values by delta.
 * Modifies node values in-place. Returns the number of nodes modified. */
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

/* Sum all values in the buffer. Returns the sum (may overflow for large values). */
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

/* Get capacity of the buffer. */
uint32_t rb_capacity(struct rb_state *rb) {
    return rb->capacity;
}

/* Get remaining space in the buffer. */
uint32_t rb_remaining(struct rb_state *rb) {
    return rb->capacity - rb->count;
}
