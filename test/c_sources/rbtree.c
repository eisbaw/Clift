#include <stdint.h>

/* Red-black tree with arena-based node storage.
 *
 * CImporter limitation: no arrays inside structs.
 * Design: separate arrays for each field, passed as pointers.
 * Tree metadata in a struct.
 *
 * Node fields stored in parallel arrays:
 *   rbt_keys[i], rbt_vals[i], rbt_left[i], rbt_right[i],
 *   rbt_parent[i], rbt_color[i]
 *
 * NULL_IDX (0xFFFFFFFF) = no node.
 * Colors: 0 = red, 1 = black.
 */

#define NULL_IDX 0xFFFFFFFF
#define RED   0
#define BLACK 1

typedef struct rbtree {
    uint32_t root;
    uint32_t count;
    uint32_t next_free;
    uint32_t capacity;
} rbtree_t;

/* Initialize an empty tree. */
void rbt_init(rbtree_t *t, uint32_t capacity) {
    t->root = NULL_IDX;
    t->count = 0;
    t->next_free = 0;
    t->capacity = capacity;
}

/* Lookup: returns value if found, 0 if not found. Sets *found. */
uint32_t rbt_lookup(rbtree_t *t, uint32_t *keys, uint32_t *vals,
                    uint32_t *lefts, uint32_t *rights,
                    uint32_t key, uint32_t *found) {
    uint32_t curr = t->root;
    *found = 0;

    while (curr != NULL_IDX) {
        if (key == keys[curr]) {
            *found = 1;
            return vals[curr];
        }
        if (key < keys[curr]) {
            curr = lefts[curr];
        } else {
            curr = rights[curr];
        }
    }

    return 0;
}

/* Left rotate at node x. */
void rbt_rotate_left(rbtree_t *t,
                     uint32_t *lefts, uint32_t *rights, uint32_t *parents,
                     uint32_t x) {
    uint32_t y;
    uint32_t xp;
    if (x == NULL_IDX) return;
    y = rights[x];
    if (y == NULL_IDX) return;

    rights[x] = lefts[y];
    if (lefts[y] != NULL_IDX) {
        parents[lefts[y]] = x;
    }

    xp = parents[x];
    parents[y] = xp;
    if (xp == NULL_IDX) {
        t->root = y;
    } else if (x == lefts[xp]) {
        lefts[xp] = y;
    } else {
        rights[xp] = y;
    }

    lefts[y] = x;
    parents[x] = y;
}

/* Right rotate at node y. */
void rbt_rotate_right(rbtree_t *t,
                      uint32_t *lefts, uint32_t *rights, uint32_t *parents,
                      uint32_t y) {
    uint32_t x;
    uint32_t yp;
    if (y == NULL_IDX) return;
    x = lefts[y];
    if (x == NULL_IDX) return;

    lefts[y] = rights[x];
    if (rights[x] != NULL_IDX) {
        parents[rights[x]] = y;
    }

    yp = parents[y];
    parents[x] = yp;
    if (yp == NULL_IDX) {
        t->root = x;
    } else if (y == lefts[yp]) {
        lefts[yp] = x;
    } else {
        rights[yp] = x;
    }

    rights[x] = y;
    parents[y] = x;
}

/* BST insert (as red leaf, no fixup). Returns 0=success, 1=full, 2=exists. */
uint32_t rbt_insert_bst(rbtree_t *t,
                        uint32_t *keys, uint32_t *vals,
                        uint32_t *lefts, uint32_t *rights,
                        uint32_t *parents, uint32_t *colors,
                        uint32_t key, uint32_t value) {
    uint32_t curr;
    uint32_t par;
    uint32_t new_node;

    if (t->root == NULL_IDX) {
        if (t->next_free >= t->capacity) return 1;
        new_node = t->next_free;
        t->next_free = t->next_free + 1;
        keys[new_node] = key;
        vals[new_node] = value;
        lefts[new_node] = NULL_IDX;
        rights[new_node] = NULL_IDX;
        parents[new_node] = NULL_IDX;
        colors[new_node] = BLACK;
        t->root = new_node;
        t->count = t->count + 1;
        return 0;
    }

    curr = t->root;
    par = NULL_IDX;

    while (curr != NULL_IDX) {
        par = curr;
        if (key == keys[curr]) {
            vals[curr] = value;
            return 2;
        }
        if (key < keys[curr]) {
            curr = lefts[curr];
        } else {
            curr = rights[curr];
        }
    }

    if (t->next_free >= t->capacity) return 1;
    new_node = t->next_free;
    t->next_free = t->next_free + 1;
    keys[new_node] = key;
    vals[new_node] = value;
    lefts[new_node] = NULL_IDX;
    rights[new_node] = NULL_IDX;
    parents[new_node] = par;
    colors[new_node] = RED;
    t->count = t->count + 1;

    if (key < keys[par]) {
        lefts[par] = new_node;
    } else {
        rights[par] = new_node;
    }

    return 0;
}

/* Get count. */
uint32_t rbt_count(rbtree_t *t) {
    return t->count;
}

/* Get minimum key (leftmost). Returns 0 if empty. */
uint32_t rbt_min(rbtree_t *t, uint32_t *keys, uint32_t *lefts) {
    uint32_t curr = t->root;
    if (curr == NULL_IDX) return 0;
    while (lefts[curr] != NULL_IDX) {
        curr = lefts[curr];
    }
    return keys[curr];
}
