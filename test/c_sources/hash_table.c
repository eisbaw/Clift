#include <stdint.h>

/* Open-addressing hash table with linear probing.
 *
 * CImporter limitation: no arrays inside structs.
 * Design: keys[] and values[] are separate pointer-based arrays
 * passed alongside the metadata struct.
 *
 * Key 0 = empty sentinel, Key 1 = deleted sentinel.
 * Capacity is passed as parameter (caller manages the arrays).
 *
 * Operations: init, insert, lookup, delete, count, contains.
 */

#define HT_EMPTY   0
#define HT_DELETED 1

typedef struct hash_table {
    uint32_t count;
    uint32_t capacity;
} hash_table_t;

/* Simple multiplicative hash (Knuth).
 * Returns index in [0, capacity-1] where capacity is a power of 2. */
uint32_t ht_hash(uint32_t key, uint32_t cap_mask) {
    uint32_t h = key * 2654435769u;
    return (h >> 16) & cap_mask;
}

/* Initialize: set all keys to HT_EMPTY, count to 0. */
void ht_init(hash_table_t *ht, uint32_t *keys, uint32_t *values,
             uint32_t capacity) {
    uint32_t i = 0;
    while (i < capacity) {
        keys[i] = HT_EMPTY;
        values[i] = 0;
        i = i + 1;
    }
    ht->count = 0;
    ht->capacity = capacity;
}

/* Insert key-value pair. Returns 0 on success, 1 if full.
 * Keys 0 and 1 are reserved; caller must not use them.
 * If key exists, updates value. */
uint32_t ht_insert(hash_table_t *ht, uint32_t *keys, uint32_t *values,
                   uint32_t key, uint32_t value) {
    uint32_t idx;
    uint32_t probes;
    uint32_t cap_mask;

    if (ht->count >= ht->capacity) {
        return 1;
    }

    cap_mask = ht->capacity - 1;
    idx = ht_hash(key, cap_mask);
    probes = 0;

    while (probes < ht->capacity) {
        if (keys[idx] == HT_EMPTY || keys[idx] == HT_DELETED) {
            keys[idx] = key;
            values[idx] = value;
            ht->count = ht->count + 1;
            return 0;
        }
        if (keys[idx] == key) {
            values[idx] = value;
            return 0;
        }
        idx = (idx + 1) & cap_mask;
        probes = probes + 1;
    }

    return 1;
}

/* Lookup key. Returns 1 if found (value in *out), 0 if not. */
uint32_t ht_lookup(hash_table_t *ht, uint32_t *keys, uint32_t *values,
                   uint32_t key, uint32_t *out) {
    uint32_t idx;
    uint32_t probes;
    uint32_t cap_mask;

    cap_mask = ht->capacity - 1;
    idx = ht_hash(key, cap_mask);
    probes = 0;

    while (probes < ht->capacity) {
        if (keys[idx] == HT_EMPTY) {
            return 0;
        }
        if (keys[idx] == key) {
            *out = values[idx];
            return 1;
        }
        idx = (idx + 1) & cap_mask;
        probes = probes + 1;
    }

    return 0;
}

/* Delete key. Returns 1 if deleted, 0 if not found. */
uint32_t ht_delete(hash_table_t *ht, uint32_t *keys, uint32_t key) {
    uint32_t idx;
    uint32_t probes;
    uint32_t cap_mask;

    cap_mask = ht->capacity - 1;
    idx = ht_hash(key, cap_mask);
    probes = 0;

    while (probes < ht->capacity) {
        if (keys[idx] == HT_EMPTY) {
            return 0;
        }
        if (keys[idx] == key) {
            keys[idx] = HT_DELETED;
            ht->count = ht->count - 1;
            return 1;
        }
        idx = (idx + 1) & cap_mask;
        probes = probes + 1;
    }

    return 0;
}

/* Return current element count. */
uint32_t ht_count(hash_table_t *ht) {
    return ht->count;
}

/* Check if key is present. Returns 1 if yes, 0 if no. */
uint32_t ht_contains(hash_table_t *ht, uint32_t *keys,
                     uint32_t key) {
    uint32_t idx;
    uint32_t probes;
    uint32_t cap_mask;

    cap_mask = ht->capacity - 1;
    idx = ht_hash(key, cap_mask);
    probes = 0;

    while (probes < ht->capacity) {
        if (keys[idx] == HT_EMPTY) {
            return 0;
        }
        if (keys[idx] == key) {
            return 1;
        }
        idx = (idx + 1) & cap_mask;
        probes = probes + 1;
    }

    return 0;
}
