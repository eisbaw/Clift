#include <stdint.h>

/* seL4 capability operations (simplified from seL4/src/kernel/)
 *
 * seL4 represents capabilities as two 64-bit words packed with bitfields.
 * The kernel extracts type tags, pointers, and rights using shift/mask ops.
 *
 * We use uint32_t to stay within Clift's uint32_t pipeline.
 * Reduced to 6 core functions to keep clift pipeline time reasonable.
 */

/* Extract capability type from bits [28:24] of word 0.
 * Real seL4: bits [63:59], 5-bit type field. MASK(5) = 0x1F */
uint32_t cap_get_capType(uint32_t w0) {
    return (w0 >> 24) & 0x1Fu;
}

/* Extract capability pointer from bits [23:0] of word 0.
 * Real seL4: bits [47:0]. MASK(24) = 0x00FFFFFF */
uint32_t cap_get_capPtr(uint32_t w0) {
    return w0 & 0x00FFFFFFu;
}

/* seL4 object type classification.
 * Returns 1 if type is an architecture object type. */
uint32_t isArchObjectType(uint32_t type) {
    if (type >= 16u) {
        if (type <= 31u) {
            return 1;
        }
    }
    return 0;
}

/* Check if a capability is a null cap (type == 0). */
uint32_t cap_is_null(uint32_t w0) {
    uint32_t capType = (w0 >> 24) & 0x1Fu;
    return capType == 0u;
}

/* Capability comparison: two caps are equal iff both words match. */
uint32_t cap_equal(uint32_t w0a, uint32_t w1a, uint32_t w0b, uint32_t w1b) {
    if (w0a == w0b) {
        if (w1a == w1b) {
            return 1;
        }
    }
    return 0;
}

/* Lookup fault: remaining bits in a CSpace lookup.
 * Simplified from seL4's lookupFault_depth_mismatch_new. */
uint32_t lookup_fault_depth_mismatch(uint32_t bitsFound, uint32_t bitsNeeded) {
    if (bitsFound >= bitsNeeded) {
        return 0;
    }
    return bitsNeeded - bitsFound;
}
