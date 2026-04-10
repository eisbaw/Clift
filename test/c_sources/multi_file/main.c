#include "common.h"

/* Check if two points are within a distance threshold */
uint32_t is_close(struct point *a, struct point *b, uint32_t threshold) {
    uint32_t d2 = distance_sq(a, b);
    if (d2 <= threshold * threshold) {
        return 1;
    }
    return 0;
}
