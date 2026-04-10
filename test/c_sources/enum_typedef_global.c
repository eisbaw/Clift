// Test: enums, typedefs, and global variables for CImporter task-0109
#include <stdint.h>

// Enum: state machine states
enum State {
    STATE_IDLE = 0,
    STATE_RUNNING = 1,
    STATE_DONE = 2,
    STATE_ERROR = 3
};

// Enum: error codes
enum ErrorCode {
    ERR_NONE = 0,
    ERR_OVERFLOW = 100,
    ERR_INVALID = 200
};

// Typedef: type alias
typedef uint32_t counter_t;
typedef uint32_t status_t;

// Global variables
uint32_t g_state = STATE_IDLE;
uint32_t g_error_count = 0;
counter_t g_iterations = 0;

// Function using enums, typedefs, and globals
uint32_t step_machine(uint32_t input) {
    if (g_state == STATE_IDLE) {
        g_state = STATE_RUNNING;
        g_iterations = 0;
    }
    if (g_state == STATE_RUNNING) {
        g_iterations = g_iterations + 1;
        if (input == 0) {
            g_state = STATE_DONE;
            return g_iterations;
        }
    }
    return 0;
}

// Function that checks error
uint32_t check_error(void) {
    if (g_state == STATE_ERROR) {
        return ERR_INVALID;
    }
    return ERR_NONE;
}
