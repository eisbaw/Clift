#include <stdint.h>

/* Compute length of a null-terminated string */
uint32_t my_strlen(const char *s) {
    uint32_t len = 0;
    while (*s != '\0') {
        len++;
        s = s + 1;
    }
    return len;
}

/* Check if first char matches */
uint32_t starts_with(const char *s, char c) {
    if (*s == c) {
        return 1;
    }
    return 0;
}
