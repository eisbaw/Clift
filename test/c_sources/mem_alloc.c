#include <stdint.h>

/* First-fit memory allocator with explicit free list.
 *
 * CImporter limitation: no arrays inside structs.
 * Design: pool is a separate uint32_t* pointer parameter.
 * Metadata in a struct (free_head, stats).
 *
 * Block layout in pool[]: header is 3 words at index i:
 *   pool[i]   = block size (including header, in words)
 *   pool[i+1] = next free block index (0xFFFFFFFF = end)
 *   pool[i+2] = allocated flag (0=free, 1=allocated)
 *   pool[i+3..i+size-1] = user data
 *
 * Operations: init, malloc, free, stats.
 */

#define NULL_IDX 0xFFFFFFFF

typedef struct mem_pool {
    uint32_t free_head;
    uint32_t total_allocated;
    uint32_t alloc_count;
    uint32_t pool_size;
} mem_pool_t;

/* Initialize: one big free block spanning the entire pool. */
void pool_init(mem_pool_t *pm, uint32_t *pool, uint32_t pool_size) {
    uint32_t hdr_idx = 0;
    pool[hdr_idx] = pool_size;     /* size = entire pool */
    pool[hdr_idx + 1] = NULL_IDX;  /* next_free = null */
    pool[hdr_idx + 2] = 0;         /* allocated = false */
    pm->free_head = 0;
    pm->total_allocated = 0;
    pm->alloc_count = 0;
    pm->pool_size = pool_size;
}

/* Allocate 'size' words. Returns index of usable memory (after header),
 * or NULL_IDX on failure. */
uint32_t pool_malloc(mem_pool_t *pm, uint32_t *pool, uint32_t req_size) {
    uint32_t prev;
    uint32_t curr;
    uint32_t needed;
    uint32_t block_size;
    uint32_t remaining;
    uint32_t new_block;

    if (req_size == 0) {
        return NULL_IDX;
    }

    needed = req_size + 3;  /* 3 words for header */
    prev = NULL_IDX;
    curr = pm->free_head;

    while (curr != NULL_IDX) {
        block_size = pool[curr];

        if (block_size >= needed) {
            remaining = block_size - needed;

            if (remaining >= 6) {
                /* Split: new free block after allocated one */
                new_block = curr + needed;
                pool[new_block] = remaining;
                pool[new_block + 1] = pool[curr + 1];
                pool[new_block + 2] = 0;

                pool[curr] = needed;

                if (prev == NULL_IDX) {
                    pm->free_head = new_block;
                } else {
                    pool[prev + 1] = new_block;
                }
            } else {
                needed = block_size;
                if (prev == NULL_IDX) {
                    pm->free_head = pool[curr + 1];
                } else {
                    pool[prev + 1] = pool[curr + 1];
                }
            }

            pool[curr + 1] = NULL_IDX;
            pool[curr + 2] = 1;
            pm->total_allocated = pm->total_allocated + needed;
            pm->alloc_count = pm->alloc_count + 1;
            return curr + 3;
        }

        prev = curr;
        curr = pool[curr + 1];
    }

    return NULL_IDX;
}

/* Free a previously allocated block. Returns 0 on success, 1 on error. */
uint32_t pool_free(mem_pool_t *pm, uint32_t *pool, uint32_t ptr) {
    uint32_t block;
    uint32_t block_size;

    if (ptr < 3 || ptr >= pm->pool_size) {
        return 1;
    }

    block = ptr - 3;
    block_size = pool[block];

    if (pool[block + 2] != 1) {
        return 1;  /* not allocated (double free) */
    }

    pool[block + 2] = 0;  /* mark free */
    pool[block + 1] = pm->free_head;
    pm->free_head = block;

    pm->total_allocated = pm->total_allocated - block_size;
    pm->alloc_count = pm->alloc_count - 1;

    return 0;
}

/* Return total words currently allocated. */
uint32_t pool_allocated(mem_pool_t *pm) {
    return pm->total_allocated;
}

/* Return number of active allocations. */
uint32_t pool_alloc_count(mem_pool_t *pm) {
    return pm->alloc_count;
}

/* Return 1 if any free space exists. */
uint32_t pool_has_free(mem_pool_t *pm) {
    return pm->free_head != NULL_IDX;
}
