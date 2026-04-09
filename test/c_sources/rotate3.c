/* rotate3: rotate three pointed-to values left
 * After: *a = old *b, *b = old *c, *c = old *a
 * Tests: multiple pointer operations, temporaries, 3-way permutation
 */
#include <stdint.h>

void rotate3(uint32_t *a, uint32_t *b, uint32_t *c) {
    uint32_t t = *a;
    *a = *b;
    *b = *c;
    *c = t;
}

/* abs_diff: absolute difference of two uint32_t values
 * Tests: conditional, arithmetic
 */
uint32_t abs_diff(uint32_t x, uint32_t y) {
    if (x > y) {
        return x - y;
    } else {
        return y - x;
    }
}

/* clamp: clamp a value to [lo, hi] range
 * Tests: multiple conditionals, comparison chains
 */
uint32_t clamp(uint32_t val, uint32_t lo, uint32_t hi) {
    if (val < lo) {
        return lo;
    } else if (val > hi) {
        return hi;
    } else {
        return val;
    }
}

/* sum_pair: sum two pointed-to values, store result in first
 * Tests: pointer read + arithmetic + pointer write
 */
void sum_pair(uint32_t *a, uint32_t *b) {
    *a = *a + *b;
}
