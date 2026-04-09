#include <stdint.h>

/* Test: do-while desugaring */
uint32_t count_digits(uint32_t n) {
    uint32_t count = 0;
    do {
        count = count + 1;
        n = n / 10;
    } while (n != 0);
    return count;
}
