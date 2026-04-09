#include <stdint.h>

/* Test: switch desugaring to nested if/else (no fall-through per StrictC) */
uint32_t classify(uint32_t x) {
    uint32_t result;
    switch (x) {
    case 0:
        result = 100;
        break;
    case 1:
        result = 200;
        break;
    case 2:
        result = 300;
        break;
    default:
        result = 999;
        break;
    }
    return result;
}
