#include <stdint.h>

/* Register overlay: access a 32-bit value */
union reg32 {
    uint32_t word;
};

/* Read the full word from a register */
uint32_t read_reg(union reg32 *r) {
    return r->word;
}

/* Void pointer: read a uint32_t through a generic pointer */
uint32_t read_via_void(void *ptr) {
    uint32_t *typed = (uint32_t *)ptr;
    return *typed;
}
