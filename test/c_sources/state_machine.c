#include <stdint.h>

/* TCP-like connection state machine.
 *
 * States: CLOSED(0), LISTEN(1), SYN_SENT(2), SYN_RCVD(3),
 *         ESTABLISHED(4), CLOSE_WAIT(5)
 *
 * Events: PASSIVE_OPEN(0), ACTIVE_OPEN(1), SYN_RECV(2),
 *         ACK_RECV(3), DATA(4), CLOSE(5)
 *
 * Guard: each transition is only valid from specific states.
 * The transition function returns the new state, or 0xFF on invalid transition.
 */

#define ST_CLOSED      0
#define ST_LISTEN      1
#define ST_SYN_SENT    2
#define ST_SYN_RCVD    3
#define ST_ESTABLISHED 4
#define ST_CLOSE_WAIT  5
#define ST_COUNT       6

#define EV_PASSIVE_OPEN 0
#define EV_ACTIVE_OPEN  1
#define EV_SYN_RECV     2
#define EV_ACK_RECV     3
#define EV_DATA         4
#define EV_CLOSE        5
#define EV_COUNT        6

#define INVALID_STATE  0xFF

typedef struct conn_state {
    uint32_t state;
    uint32_t tx_bytes;
    uint32_t rx_bytes;
    uint32_t transition_count;
} conn_state_t;

/* Initialize connection to CLOSED state. */
void conn_init(conn_state_t *conn) {
    conn->state = ST_CLOSED;
    conn->tx_bytes = 0;
    conn->rx_bytes = 0;
    conn->transition_count = 0;
}

/* Core transition function: returns new state, or INVALID_STATE.
 * This encodes the TCP state diagram (simplified). */
uint32_t conn_next_state(uint32_t current, uint32_t event) {
    /* CLOSED + PASSIVE_OPEN -> LISTEN */
    if (current == ST_CLOSED && event == EV_PASSIVE_OPEN) {
        return ST_LISTEN;
    }
    /* CLOSED + ACTIVE_OPEN -> SYN_SENT */
    if (current == ST_CLOSED && event == EV_ACTIVE_OPEN) {
        return ST_SYN_SENT;
    }
    /* LISTEN + SYN_RECV -> SYN_RCVD */
    if (current == ST_LISTEN && event == EV_SYN_RECV) {
        return ST_SYN_RCVD;
    }
    /* LISTEN + CLOSE -> CLOSED */
    if (current == ST_LISTEN && event == EV_CLOSE) {
        return ST_CLOSED;
    }
    /* SYN_SENT + SYN_RECV -> SYN_RCVD */
    if (current == ST_SYN_SENT && event == EV_SYN_RECV) {
        return ST_SYN_RCVD;
    }
    /* SYN_RCVD + ACK_RECV -> ESTABLISHED */
    if (current == ST_SYN_RCVD && event == EV_ACK_RECV) {
        return ST_ESTABLISHED;
    }
    /* SYN_RCVD + CLOSE -> CLOSED */
    if (current == ST_SYN_RCVD && event == EV_CLOSE) {
        return ST_CLOSED;
    }
    /* ESTABLISHED + DATA -> ESTABLISHED (stays, just count bytes) */
    if (current == ST_ESTABLISHED && event == EV_DATA) {
        return ST_ESTABLISHED;
    }
    /* ESTABLISHED + CLOSE -> CLOSE_WAIT */
    if (current == ST_ESTABLISHED && event == EV_CLOSE) {
        return ST_CLOSE_WAIT;
    }
    /* CLOSE_WAIT + CLOSE -> CLOSED */
    if (current == ST_CLOSE_WAIT && event == EV_CLOSE) {
        return ST_CLOSED;
    }

    return INVALID_STATE;
}

/* Apply a transition: returns 0 on success, 1 on invalid transition. */
uint32_t conn_transition(conn_state_t *conn, uint32_t event) {
    uint32_t next = conn_next_state(conn->state, event);
    if (next == INVALID_STATE) {
        return 1;
    }
    conn->state = next;
    conn->transition_count = conn->transition_count + 1;
    return 0;
}

/* Send data (only valid in ESTABLISHED). Returns 0 on success, 1 on error. */
uint32_t conn_send(conn_state_t *conn, uint32_t bytes) {
    if (conn->state != ST_ESTABLISHED) {
        return 1;
    }
    conn->tx_bytes = conn->tx_bytes + bytes;
    return 0;
}

/* Receive data (only valid in ESTABLISHED). Returns 0 on success, 1 on error. */
uint32_t conn_recv(conn_state_t *conn, uint32_t bytes) {
    if (conn->state != ST_ESTABLISHED) {
        return 1;
    }
    conn->rx_bytes = conn->rx_bytes + bytes;
    return 0;
}

/* Get current state. */
uint32_t conn_get_state(conn_state_t *conn) {
    return conn->state;
}

/* Check if connection is in a data-ready state. */
uint32_t conn_is_established(conn_state_t *conn) {
    return conn->state == ST_ESTABLISHED;
}

/* Check if state is valid (< ST_COUNT). */
uint32_t conn_state_valid(uint32_t state) {
    return state < ST_COUNT;
}

/* Get transition count. */
uint32_t conn_get_transitions(conn_state_t *conn) {
    return conn->transition_count;
}
