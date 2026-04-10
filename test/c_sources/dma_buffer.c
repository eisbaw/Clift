#include <stdint.h>

/* Circular DMA buffer with read/write pointers.
 *
 * CImporter limitation: no arrays inside structs.
 * Design: data array is a separate uint32_t* parameter.
 * Metadata (indices, count, capacity) in a struct.
 *
 * Models producer-consumer circular buffer for DMA engines.
 * Invariant: count <= capacity, indices wrap modulo capacity.
 *
 * Operations: init, write, read, available, free_space,
 *             is_empty, is_full, peek, reset.
 */

typedef struct dma_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t count;
    uint32_t capacity;
} dma_buffer_t;

/* Initialize an empty DMA buffer. */
void dma_init(dma_buffer_t *buf, uint32_t capacity) {
    buf->write_idx = 0;
    buf->read_idx = 0;
    buf->count = 0;
    buf->capacity = capacity;
}

/* Write one element. Returns 0 on success, 1 if full. */
uint32_t dma_write(dma_buffer_t *buf, uint32_t *data, uint32_t value) {
    uint32_t cap_mask;
    if (buf->count >= buf->capacity) {
        return 1;
    }
    cap_mask = buf->capacity - 1;
    data[buf->write_idx] = value;
    buf->write_idx = (buf->write_idx + 1) & cap_mask;
    buf->count = buf->count + 1;
    return 0;
}

/* Read one element. Returns 0 on success (value in *out), 1 if empty. */
uint32_t dma_read(dma_buffer_t *buf, uint32_t *data, uint32_t *out) {
    uint32_t cap_mask;
    if (buf->count == 0) {
        return 1;
    }
    cap_mask = buf->capacity - 1;
    *out = data[buf->read_idx];
    buf->read_idx = (buf->read_idx + 1) & cap_mask;
    buf->count = buf->count - 1;
    return 0;
}

/* Return number of elements available for reading. */
uint32_t dma_available(dma_buffer_t *buf) {
    return buf->count;
}

/* Return number of free slots for writing. */
uint32_t dma_free_space(dma_buffer_t *buf) {
    return buf->capacity - buf->count;
}

/* Check if buffer is empty. */
uint32_t dma_is_empty(dma_buffer_t *buf) {
    return buf->count == 0;
}

/* Check if buffer is full. */
uint32_t dma_is_full(dma_buffer_t *buf) {
    return buf->count >= buf->capacity;
}

/* Peek at next readable element without consuming. */
uint32_t dma_peek(dma_buffer_t *buf, uint32_t *data, uint32_t *out) {
    if (buf->count == 0) {
        return 1;
    }
    *out = data[buf->read_idx];
    return 0;
}

/* Reset the buffer (discard all data). */
void dma_reset(dma_buffer_t *buf) {
    buf->write_idx = 0;
    buf->read_idx = 0;
    buf->count = 0;
}

/* Write multiple elements. Returns number actually written. */
uint32_t dma_write_batch(dma_buffer_t *buf, uint32_t *data,
                         uint32_t *values, uint32_t n) {
    uint32_t written = 0;
    uint32_t cap_mask;
    cap_mask = buf->capacity - 1;

    while (written < n) {
        if (buf->count >= buf->capacity) {
            return written;
        }
        data[buf->write_idx] = values[written];
        buf->write_idx = (buf->write_idx + 1) & cap_mask;
        buf->count = buf->count + 1;
        written = written + 1;
    }
    return written;
}
