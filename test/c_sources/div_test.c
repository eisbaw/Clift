#include <stdint.h>

/* Test: division and modulo operations should get UB guards for divisor == 0 */
uint32_t safe_div(uint32_t a, uint32_t b) {
    return a / b;
}

uint32_t safe_mod(uint32_t a, uint32_t b) {
    return a % b;
}
