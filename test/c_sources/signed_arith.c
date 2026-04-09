#include <stdint.h>

/* Test: signed arithmetic should get overflow UB guards */
int32_t signed_add(int32_t a, int32_t b) {
    return a + b;
}

int32_t signed_sub(int32_t a, int32_t b) {
    return a - b;
}

int32_t signed_mul(int32_t a, int32_t b) {
    return a * b;
}

int32_t signed_div(int32_t a, int32_t b) {
    return a / b;
}
