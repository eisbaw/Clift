#include <stdint.h>

/* Extract bits [hi:lo] from val (inclusive, 0-indexed) */
uint32_t extract_bits(uint32_t val, uint32_t lo, uint32_t hi) {
    uint32_t mask = ((1u << (hi - lo + 1)) - 1) << lo;
    return (val & mask) >> lo;
}

/* Set bit n in val */
uint32_t set_bit(uint32_t val, uint32_t n) {
    return val | (1u << n);
}

/* Clear bit n in val */
uint32_t clear_bit(uint32_t val, uint32_t n) {
    return val & ~(1u << n);
}

/* Toggle bit n in val */
uint32_t toggle_bit(uint32_t val, uint32_t n) {
    return val ^ (1u << n);
}

/* Combine two 16-bit halves into a 32-bit word */
uint32_t combine_halves(uint32_t lo_half, uint32_t hi_half) {
    return (hi_half << 16) | lo_half;
}
