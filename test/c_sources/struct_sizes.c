/* Test structs for differential testing of CImporter struct layout.
 * Compile with: gcc -o struct_sizes struct_sizes.c && ./struct_sizes
 * Compares against CImporter's computed sizes and offsets.
 */
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>

/* Test 1: Simple struct with no padding */
struct simple {
    uint32_t a;
    uint32_t b;
};

/* Test 2: Struct with padding (alignment gap between fields) */
struct padded {
    uint8_t x;
    uint32_t y;
};

/* Test 3: Struct with pointer (self-referential linked list node) */
struct node {
    int val;
    struct node *next;
};

/* Test 4: Struct with mixed sizes requiring alignment */
struct mixed {
    uint8_t a;
    uint16_t b;
    uint32_t c;
    uint64_t d;
};

/* Test 5: Struct with trailing padding */
struct trailing_pad {
    uint64_t x;
    uint8_t y;
};

/* Test 6: All-pointer struct */
struct ptr_pair {
    uint32_t *a;
    uint32_t *b;
};

int main(void) {
    /* Format: struct_name,sizeof,field_name,offsetof */
    printf("STRUCT simple %zu %zu\n", sizeof(struct simple), _Alignof(struct simple));
    printf("FIELD simple a %zu\n", offsetof(struct simple, a));
    printf("FIELD simple b %zu\n", offsetof(struct simple, b));

    printf("STRUCT padded %zu %zu\n", sizeof(struct padded), _Alignof(struct padded));
    printf("FIELD padded x %zu\n", offsetof(struct padded, x));
    printf("FIELD padded y %zu\n", offsetof(struct padded, y));

    printf("STRUCT node %zu %zu\n", sizeof(struct node), _Alignof(struct node));
    printf("FIELD node val %zu\n", offsetof(struct node, val));
    printf("FIELD node next %zu\n", offsetof(struct node, next));

    printf("STRUCT mixed %zu %zu\n", sizeof(struct mixed), _Alignof(struct mixed));
    printf("FIELD mixed a %zu\n", offsetof(struct mixed, a));
    printf("FIELD mixed b %zu\n", offsetof(struct mixed, b));
    printf("FIELD mixed c %zu\n", offsetof(struct mixed, c));
    printf("FIELD mixed d %zu\n", offsetof(struct mixed, d));

    printf("STRUCT trailing_pad %zu %zu\n", sizeof(struct trailing_pad), _Alignof(struct trailing_pad));
    printf("FIELD trailing_pad x %zu\n", offsetof(struct trailing_pad, x));
    printf("FIELD trailing_pad y %zu\n", offsetof(struct trailing_pad, y));

    printf("STRUCT ptr_pair %zu %zu\n", sizeof(struct ptr_pair), _Alignof(struct ptr_pair));
    printf("FIELD ptr_pair a %zu\n", offsetof(struct ptr_pair, a));
    printf("FIELD ptr_pair b %zu\n", offsetof(struct ptr_pair, b));

    return 0;
}
