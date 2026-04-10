/* Task 0141: Integer promotion edge case tests.
 *
 * Tests C11 integer promotion rules (6.3.1.1) and usual arithmetic
 * conversions (6.3.1.8) that the CImporter must handle correctly.
 *
 * Each function tests a specific promotion edge case.
 * Expected behavior documented in comments.
 */

#include <stdint.h>

/* Test 1: uint8_t + uint8_t promotes to int (C11 6.3.1.1p2)
 * 200 + 200 = 400 in int, then assigned to uint32_t.
 * If promotions are wrong, result would be 144 (uint8_t wrapping). */
uint32_t test_uint8_addition(uint8_t a, uint8_t b) {
    uint32_t c = a + b;
    return c;
}

/* Test 2: int8_t + uint8_t (signed + unsigned promotion)
 * Both promote to int first (C11 6.3.1.8).
 * -1 + 200 = 199 in int. */
int32_t test_mixed_sign_add(int8_t a, uint8_t b) {
    int32_t c = a + b;
    return c;
}

/* Test 3: uint16_t * uint16_t may overflow int
 * Both promote to int (32-bit signed). 60000 * 60000 = 3600000000
 * which overflows int32_t (max 2147483647). This is UB in C.
 * Our model should guard against this. */
uint32_t test_uint16_multiply(uint16_t a, uint16_t b) {
    uint32_t c = (uint32_t)a * (uint32_t)b;
    return c;
}

/* Test 4: uint32_t - uint32_t (unsigned wrapping)
 * 5 - 10 = 4294967291 (wraps around, not UB for unsigned) */
uint32_t test_unsigned_wrap(uint32_t a, uint32_t b) {
    return a - b;
}

/* Test 5: Comparison between signed and unsigned
 * -1 < 0u: -1 converts to UINT_MAX, so (-1 < 0u) is FALSE.
 * Our model maps signed to unsigned, so this should work. */
uint32_t test_signed_unsigned_compare(int32_t a, uint32_t b) {
    if (a < (int32_t)b) {
        return 1;
    }
    return 0;
}

/* Test 6: Shift operations - type of result is type of left operand
 * uint8_t << 8 promotes uint8_t to int first, then shifts.
 * 1 << 8 = 256 (fits in int), assigned to uint32_t. */
uint32_t test_shift_promotion(uint8_t a) {
    uint32_t c = (uint32_t)a << 8;
    return c;
}

/* Test 7: Unary minus on unsigned
 * -(uint32_t)1 = 4294967295 (modular arithmetic). */
uint32_t test_unary_minus_unsigned(uint32_t a) {
    return 0 - a;
}

/* Test 8: Widening from uint8 to uint64 */
uint64_t test_widen_u8_to_u64(uint8_t a) {
    uint64_t c = a;
    return c;
}
