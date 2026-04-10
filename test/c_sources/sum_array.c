#include <stdint.h>

// Sum elements of an array: s = arr[0] + arr[1] + ... + arr[len-1]
uint32_t sum_array(uint32_t *arr, uint32_t len) {
    uint32_t s = 0;
    uint32_t i = 0;
    while (i < len) {
        s = s + arr[i];
        i = i + 1;
    }
    return s;
}
