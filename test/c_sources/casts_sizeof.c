#include <stdint.h>
#include <stddef.h>

/* Widening cast: uint8 -> uint32 */
uint32_t widen_u8_to_u32(uint8_t x) {
    return (uint32_t)x;
}

/* Narrowing cast: uint32 -> uint8 (lossy) */
uint8_t narrow_u32_to_u8(uint32_t x) {
    return (uint8_t)x;
}

/* sizeof(type) usage */
uint32_t size_of_uint32(void) {
    return (uint32_t)sizeof(uint32_t);
}

/* sizeof(expr) usage */
uint32_t size_of_var(uint64_t x) {
    return (uint32_t)sizeof(x);
}

/* Mixed-width arithmetic with casts */
uint32_t mixed_arith(uint8_t a, uint16_t b) {
    uint32_t result = (uint32_t)a + (uint32_t)b;
    return result;
}
