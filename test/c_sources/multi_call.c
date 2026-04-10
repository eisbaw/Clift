/* Multi-function C file for testing inter-procedural calls.
 * Tests: direct calls, calls with return values, helper functions.
 *
 * 5 functions:
 *   - add(a, b): returns a + b
 *   - double_val(x): returns add(x, x)
 *   - max(a, b): returns a > b ? a : b
 *   - clamp(x, lo, hi): uses max and min-like logic
 *   - sum3(a, b, c): chains add calls
 */

#include <stdint.h>

uint32_t add(uint32_t a, uint32_t b) {
    return a + b;
}

uint32_t double_val(uint32_t x) {
    uint32_t result = add(x, x);
    return result;
}

uint32_t max_val(uint32_t a, uint32_t b) {
    if (a > b) {
        return a;
    }
    return b;
}

uint32_t clamp(uint32_t x, uint32_t lo, uint32_t hi) {
    uint32_t result = max_val(x, lo);
    if (result > hi) {
        result = hi;
    }
    return result;
}

uint32_t sum3(uint32_t a, uint32_t b, uint32_t c) {
    uint32_t ab = add(a, b);
    uint32_t abc = add(ab, c);
    return abc;
}
