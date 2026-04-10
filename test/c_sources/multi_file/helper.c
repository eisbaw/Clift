#include "common.h"

/* Compute squared distance between two points */
uint32_t distance_sq(struct point *a, struct point *b) {
    uint32_t dx = a->x - b->x;
    uint32_t dy = a->y - b->y;
    return dx * dx + dy * dy;
}
