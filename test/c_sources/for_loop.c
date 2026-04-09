#include <stdint.h>

/* Test: for loop desugaring to while */
uint32_t sum_to_n(uint32_t n) {
    uint32_t sum = 0;
    for (uint32_t i = 0; i < n; i++) {
        sum = sum + i;
    }
    return sum;
}
