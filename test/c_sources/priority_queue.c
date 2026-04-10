#include <stdint.h>

/* Binary min-heap priority queue.
 *
 * CImporter limitation: no arrays inside structs.
 * Design: data array is a separate uint32_t* parameter.
 * Metadata (size, capacity) in a struct.
 *
 * Array-based heap: children of node i at 2i+1, 2i+2.
 * Parent of node i at (i-1)/2.
 * Heap property: parent <= both children.
 *
 * Operations: init, insert, extract_min, peek, size, is_empty, is_full.
 */

typedef struct pqueue {
    uint32_t size;
    uint32_t capacity;
} pqueue_t;

/* Initialize an empty priority queue. */
void pq_init(pqueue_t *pq, uint32_t capacity) {
    pq->size = 0;
    pq->capacity = capacity;
}

/* Swap two elements. */
void pq_swap(uint32_t *data, uint32_t i, uint32_t j) {
    uint32_t tmp = data[i];
    data[i] = data[j];
    data[j] = tmp;
}

/* Bubble up: restore heap property after insertion at index i. */
void pq_bubble_up(uint32_t *data, uint32_t i) {
    uint32_t parent;
    while (i > 0) {
        parent = (i - 1) / 2;
        if (data[i] < data[parent]) {
            pq_swap(data, i, parent);
            i = parent;
        } else {
            return;
        }
    }
}

/* Bubble down: restore heap property from index i.
 * Loop bounded by size (max depth of heap). */
void pq_bubble_down(uint32_t *data, uint32_t heap_size, uint32_t i) {
    uint32_t left;
    uint32_t right;
    uint32_t smallest;
    uint32_t iters = 0;

    while (iters < heap_size) {
        left = 2 * i + 1;
        right = 2 * i + 2;
        smallest = i;

        if (left < heap_size && data[left] < data[smallest]) {
            smallest = left;
        }
        if (right < heap_size && data[right] < data[smallest]) {
            smallest = right;
        }

        if (smallest == i) {
            return;
        }

        pq_swap(data, i, smallest);
        i = smallest;
        iters = iters + 1;
    }
}

/* Insert a value. Returns 0 on success, 1 if full. */
uint32_t pq_insert(pqueue_t *pq, uint32_t *data, uint32_t value) {
    if (pq->size >= pq->capacity) {
        return 1;
    }
    data[pq->size] = value;
    pq_bubble_up(data, pq->size);
    pq->size = pq->size + 1;
    return 0;
}

/* Extract minimum. Returns 0 on success (value in *out), 1 if empty. */
uint32_t pq_extract_min(pqueue_t *pq, uint32_t *data, uint32_t *out) {
    uint32_t root_idx = 0;
    if (pq->size == 0) {
        return 1;
    }
    *out = data[root_idx];
    pq->size = pq->size - 1;
    if (pq->size > 0) {
        data[root_idx] = data[pq->size];
        pq_bubble_down(data, pq->size, root_idx);
    }
    return 0;
}

/* Peek at minimum without removing. Returns 0 on success, 1 if empty. */
uint32_t pq_peek(pqueue_t *pq, uint32_t *data, uint32_t *out) {
    uint32_t root_idx = 0;
    if (pq->size == 0) {
        return 1;
    }
    *out = data[root_idx];
    return 0;
}

/* Return current size. */
uint32_t pq_size(pqueue_t *pq) {
    return pq->size;
}

/* Check if empty. */
uint32_t pq_is_empty(pqueue_t *pq) {
    return pq->size == 0;
}

/* Check if full. */
uint32_t pq_is_full(pqueue_t *pq) {
    return pq->size >= pq->capacity;
}
