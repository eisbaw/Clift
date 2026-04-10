#ifndef COMMON_H
#define COMMON_H

#include <stdint.h>

/* Shared struct: used by both helper.c and main.c */
struct point {
    uint32_t x;
    uint32_t y;
};

/* Declared in helper.c */
uint32_t distance_sq(struct point *a, struct point *b);

/* Declared in main.c */
uint32_t is_close(struct point *a, struct point *b, uint32_t threshold);

#endif
