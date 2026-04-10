/* uart_driver.c -- Realistic UART driver with MMIO register manipulation
 *
 * Faithfully represents embedded UART driver patterns:
 * - Memory-mapped I/O registers (modeled as struct fields read via pointers)
 * - Baud rate configuration with divisor calculation
 * - Status register bit manipulation
 * - Send/receive with busy-wait polling
 * - FIFO buffer for interrupt-driven receive
 * - Driver state machine (uninit -> configured -> active -> error)
 *
 * Constraints (CImporter subset):
 *   - No arrays: receive buffer modeled as linked list
 *   - No volatile (CImporter doesn't handle it, but MMIO pattern preserved)
 *   - No floating point, goto, longjmp, VLAs
 */

#include <stdint.h>
#include <stddef.h>

/* ================================================================
 * Register definitions (simulating MMIO register layout)
 * ================================================================ */

/* UART register block -- in real hardware this would be at a fixed address.
 * We model it as a struct accessed via pointer. */
struct uart_regs {
    uint32_t data;     /* TX/RX data register (offset 0x00) */
    uint32_t status;   /* Status register (offset 0x04) */
    uint32_t control;  /* Control register (offset 0x08) */
    uint32_t baud_div; /* Baud rate divisor (offset 0x0C) */
    uint32_t int_en;   /* Interrupt enable register (offset 0x10) */
    uint32_t int_flag; /* Interrupt flag register (offset 0x14) */
};

/* Status register bits */
#define UART_SR_TXRDY   0x01   /* Transmitter ready */
#define UART_SR_RXRDY   0x02   /* Receiver has data */
#define UART_SR_TXEMPTY 0x04   /* Transmit shift register empty */
#define UART_SR_OVRE    0x08   /* Overrun error */
#define UART_SR_FRAME   0x10   /* Framing error */
#define UART_SR_PARE    0x20   /* Parity error */

/* Control register bits */
#define UART_CR_TXEN    0x01   /* Transmitter enable */
#define UART_CR_RXEN    0x02   /* Receiver enable */
#define UART_CR_RSTRX   0x04   /* Reset receiver */
#define UART_CR_RSTTX   0x08   /* Reset transmitter */
#define UART_CR_RSTSTA  0x10   /* Reset status bits */

/* Interrupt enable bits */
#define UART_IE_RXRDY   0x01   /* RX ready interrupt */
#define UART_IE_TXRDY   0x02   /* TX ready interrupt */
#define UART_IE_OVRE    0x04   /* Overrun error interrupt */

/* ================================================================
 * Driver state
 * ================================================================ */

/* Driver states */
#define DRV_UNINIT      0
#define DRV_CONFIGURED  1
#define DRV_ACTIVE      2
#define DRV_ERROR       3

/* Receive buffer node */
struct rx_node {
    uint32_t byte_val;
    struct rx_node *next;
};

/* Driver context */
struct uart_driver {
    struct uart_regs *regs;    /* Pointer to MMIO register block */
    uint32_t state;            /* Driver state machine */
    uint32_t baud_rate;        /* Configured baud rate */
    uint32_t clock_freq;       /* Peripheral clock frequency */
    uint32_t tx_count;         /* Total bytes transmitted */
    uint32_t rx_count;         /* Total bytes received */
    uint32_t error_count;      /* Total errors detected */
    struct rx_node *rx_head;   /* Receive buffer head */
    struct rx_node *rx_tail;   /* Receive buffer tail */
    uint32_t rx_buf_count;     /* Bytes in receive buffer */
    uint32_t rx_buf_capacity;  /* Max receive buffer size */
};

/* Error codes */
#define UART_OK          0
#define UART_ERR_STATE   1
#define UART_ERR_PARAM   2
#define UART_ERR_BUSY    3
#define UART_ERR_OVERRUN 4
#define UART_ERR_FRAME   5
#define UART_ERR_PARITY  6
#define UART_ERR_BUFFUL  7

/* ================================================================
 * Initialization
 * ================================================================ */

/* Initialize the UART driver. Must be called before any other operation. */
uint32_t uart_init(struct uart_driver *drv, struct uart_regs *regs,
                   uint32_t clock_freq, uint32_t rx_capacity) {
    if (clock_freq == 0) {
        return UART_ERR_PARAM;
    }
    if (rx_capacity == 0) {
        return UART_ERR_PARAM;
    }
    drv->regs = regs;
    drv->state = DRV_UNINIT;
    drv->baud_rate = 0;
    drv->clock_freq = clock_freq;
    drv->tx_count = 0;
    drv->rx_count = 0;
    drv->error_count = 0;
    drv->rx_head = NULL;
    drv->rx_tail = NULL;
    drv->rx_buf_count = 0;
    drv->rx_buf_capacity = rx_capacity;
    return UART_OK;
}

/* ================================================================
 * Configuration
 * ================================================================ */

/* Configure baud rate. Divisor = clock_freq / (16 * baud_rate).
 * Must be called before uart_enable(). */
uint32_t uart_set_baud(struct uart_driver *drv, uint32_t baud_rate) {
    uint32_t divisor;
    uint32_t denominator;
    if (baud_rate == 0) {
        return UART_ERR_PARAM;
    }
    if (drv->state == DRV_ACTIVE) {
        return UART_ERR_STATE;
    }
    denominator = 16 * baud_rate;
    if (denominator == 0) {
        return UART_ERR_PARAM;
    }
    divisor = drv->clock_freq / denominator;
    if (divisor == 0) {
        return UART_ERR_PARAM;
    }
    drv->regs->baud_div = divisor;
    drv->baud_rate = baud_rate;
    drv->state = DRV_CONFIGURED;
    return UART_OK;
}

/* Enable the UART (start transmitter and receiver). */
uint32_t uart_enable(struct uart_driver *drv) {
    uint32_t cr;
    if (drv->state != DRV_CONFIGURED) {
        return UART_ERR_STATE;
    }
    /* Reset then enable TX and RX */
    cr = UART_CR_RSTRX | UART_CR_RSTTX | UART_CR_RSTSTA;
    drv->regs->control = cr;
    cr = UART_CR_TXEN | UART_CR_RXEN;
    drv->regs->control = cr;
    /* Enable RX ready interrupt */
    drv->regs->int_en = UART_IE_RXRDY | UART_IE_OVRE;
    drv->state = DRV_ACTIVE;
    return UART_OK;
}

/* Disable the UART. */
uint32_t uart_disable(struct uart_driver *drv) {
    if (drv->state != DRV_ACTIVE) {
        return UART_ERR_STATE;
    }
    drv->regs->control = 0;
    drv->regs->int_en = 0;
    drv->state = DRV_CONFIGURED;
    return UART_OK;
}

/* ================================================================
 * Transmit
 * ================================================================ */

/* Send a single byte. Polls TXRDY status bit. */
uint32_t uart_send_byte(struct uart_driver *drv, uint32_t byte_val) {
    uint32_t sr;
    if (drv->state != DRV_ACTIVE) {
        return UART_ERR_STATE;
    }
    /* Check transmitter ready */
    sr = drv->regs->status;
    if ((sr & UART_SR_TXRDY) == 0) {
        return UART_ERR_BUSY;
    }
    drv->regs->data = byte_val & 0xFF;
    drv->tx_count = drv->tx_count + 1;
    return UART_OK;
}

/* ================================================================
 * Receive
 * ================================================================ */

/* Check for and handle a received byte (poll mode).
 * If data is available, stores it in the receive buffer. */
uint32_t uart_poll_rx(struct uart_driver *drv, struct rx_node *node) {
    uint32_t sr;
    uint32_t data;
    if (drv->state != DRV_ACTIVE) {
        return UART_ERR_STATE;
    }
    sr = drv->regs->status;
    /* Check for errors first */
    if ((sr & UART_SR_OVRE) != 0) {
        drv->error_count = drv->error_count + 1;
        /* Clear error by writing RSTSTA to control */
        drv->regs->control = UART_CR_RSTSTA | UART_CR_TXEN | UART_CR_RXEN;
        return UART_ERR_OVERRUN;
    }
    if ((sr & UART_SR_FRAME) != 0) {
        drv->error_count = drv->error_count + 1;
        drv->regs->control = UART_CR_RSTSTA | UART_CR_TXEN | UART_CR_RXEN;
        return UART_ERR_FRAME;
    }
    /* Check for data */
    if ((sr & UART_SR_RXRDY) == 0) {
        return UART_ERR_BUSY;  /* No data available */
    }
    /* Check buffer space */
    if (drv->rx_buf_count >= drv->rx_buf_capacity) {
        return UART_ERR_BUFFUL;
    }
    /* Read data and add to buffer */
    data = drv->regs->data & 0xFF;
    node->byte_val = data;
    node->next = NULL;
    if (drv->rx_tail != NULL) {
        drv->rx_tail->next = node;
    }
    drv->rx_tail = node;
    if (drv->rx_head == NULL) {
        drv->rx_head = node;
    }
    drv->rx_buf_count = drv->rx_buf_count + 1;
    drv->rx_count = drv->rx_count + 1;
    return UART_OK;
}

/* Read one byte from the receive buffer.
 * Returns the byte value in *out_byte. */
uint32_t uart_read_byte(struct uart_driver *drv, uint32_t *out_byte) {
    struct rx_node *front;
    if (drv->rx_head == NULL) {
        return UART_ERR_BUSY;
    }
    front = drv->rx_head;
    *out_byte = front->byte_val;
    drv->rx_head = front->next;
    if (drv->rx_head == NULL) {
        drv->rx_tail = NULL;
    }
    front->next = NULL;
    drv->rx_buf_count = drv->rx_buf_count - 1;
    return UART_OK;
}

/* ================================================================
 * Status queries
 * ================================================================ */

/* Get driver state. */
uint32_t uart_get_state(struct uart_driver *drv) {
    return drv->state;
}

/* Get total bytes transmitted. */
uint32_t uart_get_tx_count(struct uart_driver *drv) {
    return drv->tx_count;
}

/* Get total bytes received. */
uint32_t uart_get_rx_count(struct uart_driver *drv) {
    return drv->rx_count;
}

/* Get error count. */
uint32_t uart_get_error_count(struct uart_driver *drv) {
    return drv->error_count;
}

/* Get receive buffer fill level. */
uint32_t uart_rx_buf_level(struct uart_driver *drv) {
    return drv->rx_buf_count;
}

/* Check if receive buffer is empty. */
uint32_t uart_rx_buf_empty(struct uart_driver *drv) {
    if (drv->rx_buf_count == 0) {
        return 1;
    }
    return 0;
}

/* Check for any error condition in status register. */
uint32_t uart_check_errors(struct uart_driver *drv) {
    uint32_t sr;
    uint32_t errors;
    sr = drv->regs->status;
    errors = sr & (UART_SR_OVRE | UART_SR_FRAME | UART_SR_PARE);
    if (errors != 0) {
        drv->state = DRV_ERROR;
        return 1;
    }
    return 0;
}

/* Reset from error state back to configured. */
uint32_t uart_reset_error(struct uart_driver *drv) {
    if (drv->state != DRV_ERROR) {
        return UART_ERR_STATE;
    }
    drv->regs->control = UART_CR_RSTSTA | UART_CR_RSTRX | UART_CR_RSTTX;
    drv->state = DRV_CONFIGURED;
    return UART_OK;
}
