/* packet_parser.c -- Ethernet + IPv4 header parser with bounds checking
 *
 * Faithfully represents network protocol parser patterns:
 * - Fixed-size header extraction from byte stream
 * - Bounds checking against buffer length at every step
 * - Bitfield extraction (IP version, IHL, flags, fragment offset)
 * - Error codes for every malformed input case
 *
 * Constraints (CImporter StrictC subset):
 *   - No arrays: buffer modeled as linked list of bytes
 *   - No address-of (&) on anything -- all output via struct pointer params
 *   - No floating point, goto, longjmp, VLAs
 *   - No pointer-to-pointer
 */

#include <stdint.h>
#include <stddef.h>

/* ================================================================
 * Data structures
 * ================================================================ */

/* Byte node in a packet buffer (simulates array access) */
struct pkt_byte {
    uint32_t value;       /* Byte value (0-255) */
    struct pkt_byte *next;
};

/* Packet buffer: a linked list of bytes with known length */
struct pkt_buffer {
    struct pkt_byte *data;
    uint32_t length;
};

/* Parsed Ethernet header (14 bytes) */
struct eth_header {
    uint32_t dst_mac_hi;   /* Destination MAC bytes 0-3 as uint32 */
    uint32_t dst_mac_lo;   /* Destination MAC bytes 4-5 (upper 16 bits) */
    uint32_t src_mac_hi;   /* Source MAC bytes 0-3 */
    uint32_t src_mac_lo;   /* Source MAC bytes 4-5 (upper 16 bits) */
    uint32_t ethertype;    /* EtherType (e.g., 0x0800 = IPv4) */
};

/* Parsed IPv4 header (20 bytes minimum) */
struct ipv4_header {
    uint32_t version;      /* IP version (should be 4) */
    uint32_t ihl;          /* Internet Header Length in 32-bit words */
    uint32_t dscp;         /* Differentiated Services Code Point */
    uint32_t total_length; /* Total packet length */
    uint32_t identification;
    uint32_t flags;        /* 3-bit flags field */
    uint32_t frag_offset;  /* Fragment offset */
    uint32_t ttl;          /* Time to live */
    uint32_t protocol;     /* Protocol (6=TCP, 17=UDP) */
    uint32_t checksum;     /* Header checksum */
    uint32_t src_addr;     /* Source IP address */
    uint32_t dst_addr;     /* Destination IP address */
};

/* Scratch space for reading multi-byte values (avoids address-of locals) */
struct read_scratch {
    uint32_t b0;
    uint32_t b1;
    uint32_t b2;
    uint32_t b3;
    uint32_t result;
};

/* Parse status holder */
struct parse_status {
    uint32_t code;
    uint32_t payload_offset;
};

/* Error codes */
#define PARSE_OK             0
#define PARSE_ERR_SHORT      1   /* Buffer too short */
#define PARSE_ERR_ETHERTYPE  2   /* Not IPv4 */
#define PARSE_ERR_VERSION    3   /* Not IPv4 version */
#define PARSE_ERR_IHL        4   /* IHL too small */
#define PARSE_ERR_LENGTH     5   /* Total length mismatch */
#define PARSE_ERR_CHECKSUM   6   /* Checksum failed */
#define PARSE_ERR_TRUNC      7   /* Packet truncated */
#define PARSE_ERR_NULL       8   /* Null pointer */

/* ================================================================
 * Buffer access helpers
 * ================================================================ */

/* Read byte at offset n from buffer by traversal.
 * Stores byte in scratch->result. Returns 0 on success, 1 if out of bounds. */
uint32_t pkt_read_byte(struct pkt_buffer *buf, uint32_t offset,
                       struct read_scratch *scratch) {
    struct pkt_byte *cur;
    uint32_t idx;
    if (offset >= buf->length) {
        return 1;
    }
    idx = 0;
    cur = buf->data;
    while (cur != NULL) {
        if (idx == offset) {
            scratch->result = cur->value & 0xFF;
            return 0;
        }
        idx = idx + 1;
        cur = cur->next;
    }
    return 1;
}

/* Read a big-endian uint16 at the given offset.
 * Stores result in scratch->result. Returns 0 on success. */
uint32_t pkt_read_u16be(struct pkt_buffer *buf, uint32_t offset,
                        struct read_scratch *scratch) {
    uint32_t rc;
    uint32_t hi;
    uint32_t lo;
    rc = pkt_read_byte(buf, offset, scratch);
    if (rc != 0) { return 1; }
    hi = scratch->result;
    rc = pkt_read_byte(buf, offset + 1, scratch);
    if (rc != 0) { return 1; }
    lo = scratch->result;
    scratch->result = (hi << 8) | lo;
    return 0;
}

/* Read a big-endian uint32 at the given offset.
 * Stores result in scratch->result. Returns 0 on success. */
uint32_t pkt_read_u32be(struct pkt_buffer *buf, uint32_t offset,
                        struct read_scratch *scratch) {
    uint32_t rc;
    uint32_t byte0;
    uint32_t byte1;
    uint32_t byte2;
    uint32_t byte3;
    rc = pkt_read_byte(buf, offset, scratch);
    if (rc != 0) { return 1; }
    byte0 = scratch->result;
    rc = pkt_read_byte(buf, offset + 1, scratch);
    if (rc != 0) { return 1; }
    byte1 = scratch->result;
    rc = pkt_read_byte(buf, offset + 2, scratch);
    if (rc != 0) { return 1; }
    byte2 = scratch->result;
    rc = pkt_read_byte(buf, offset + 3, scratch);
    if (rc != 0) { return 1; }
    byte3 = scratch->result;
    scratch->result = (byte0 << 24) | (byte1 << 16) | (byte2 << 8) | byte3;
    return 0;
}

/* ================================================================
 * Ethernet header parsing
 * ================================================================ */

/* Parse Ethernet header (14 bytes). */
uint32_t parse_eth_header(struct pkt_buffer *buf, struct eth_header *eth,
                          struct read_scratch *scratch) {
    uint32_t rc;
    if (buf->length < 14) {
        return PARSE_ERR_SHORT;
    }
    rc = pkt_read_u32be(buf, 0, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    eth->dst_mac_hi = scratch->result;
    rc = pkt_read_u16be(buf, 4, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    eth->dst_mac_lo = scratch->result;
    rc = pkt_read_u32be(buf, 6, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    eth->src_mac_hi = scratch->result;
    rc = pkt_read_u16be(buf, 10, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    eth->src_mac_lo = scratch->result;
    rc = pkt_read_u16be(buf, 12, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    eth->ethertype = scratch->result;
    return PARSE_OK;
}

/* ================================================================
 * IPv4 header parsing
 * ================================================================ */

/* Parse IPv4 header at offset. Validates version==4, IHL>=5. */
uint32_t parse_ipv4_header(struct pkt_buffer *buf, uint32_t offset,
                           struct ipv4_header *ip,
                           struct read_scratch *scratch) {
    uint32_t rc;
    uint32_t byte0;
    uint32_t byte1;
    uint32_t hdr_len_bytes;
    uint32_t tmp;

    if (buf->length < offset + 20) {
        return PARSE_ERR_SHORT;
    }
    rc = pkt_read_byte(buf, offset, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    byte0 = scratch->result;
    ip->version = (byte0 >> 4) & 0x0F;
    ip->ihl = byte0 & 0x0F;
    if (ip->version != 4) {
        return PARSE_ERR_VERSION;
    }
    if (ip->ihl < 5) {
        return PARSE_ERR_IHL;
    }
    hdr_len_bytes = ip->ihl * 4;
    rc = pkt_read_byte(buf, offset + 1, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    byte1 = scratch->result;
    ip->dscp = byte1 >> 2;
    rc = pkt_read_u16be(buf, offset + 2, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    ip->total_length = scratch->result;
    if (ip->total_length < hdr_len_bytes) {
        return PARSE_ERR_LENGTH;
    }
    rc = pkt_read_u16be(buf, offset + 4, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    ip->identification = scratch->result;
    rc = pkt_read_u16be(buf, offset + 6, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    tmp = scratch->result;
    ip->flags = (tmp >> 13) & 0x07;
    ip->frag_offset = tmp & 0x1FFF;
    rc = pkt_read_byte(buf, offset + 8, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    ip->ttl = scratch->result;
    rc = pkt_read_byte(buf, offset + 9, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    ip->protocol = scratch->result;
    rc = pkt_read_u16be(buf, offset + 10, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    ip->checksum = scratch->result;
    rc = pkt_read_u32be(buf, offset + 12, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    ip->src_addr = scratch->result;
    rc = pkt_read_u32be(buf, offset + 16, scratch);
    if (rc != 0) { return PARSE_ERR_SHORT; }
    ip->dst_addr = scratch->result;
    return PARSE_OK;
}

/* ================================================================
 * Full packet parsing
 * ================================================================ */

/* Parse Ethernet+IPv4 packet. All output structs passed as separate pointers. */
uint32_t parse_packet(struct pkt_buffer *buf,
                      struct eth_header *eth,
                      struct ipv4_header *ip,
                      struct parse_status *status,
                      struct read_scratch *scratch) {
    uint32_t rc;
    uint32_t ip_offset;
    uint32_t hdr_len;

    if (buf->data == NULL) {
        status->code = PARSE_ERR_NULL;
        return PARSE_ERR_NULL;
    }
    if (buf->length == 0) {
        status->code = PARSE_ERR_SHORT;
        return PARSE_ERR_SHORT;
    }
    rc = parse_eth_header(buf, eth, scratch);
    if (rc != 0) {
        status->code = rc;
        return rc;
    }
    if (eth->ethertype != 0x0800) {
        status->code = PARSE_ERR_ETHERTYPE;
        return PARSE_ERR_ETHERTYPE;
    }
    ip_offset = 14;
    rc = parse_ipv4_header(buf, ip_offset, ip, scratch);
    if (rc != 0) {
        status->code = rc;
        return rc;
    }
    hdr_len = ip->ihl * 4;
    if (buf->length < ip_offset + ip->total_length) {
        status->code = PARSE_ERR_TRUNC;
        return PARSE_ERR_TRUNC;
    }
    status->payload_offset = ip_offset + hdr_len;
    status->code = PARSE_OK;
    return PARSE_OK;
}

/* ================================================================
 * Utility functions
 * ================================================================ */

/* Get buffer length. */
uint32_t pkt_buffer_length(struct pkt_buffer *buf) {
    return buf->length;
}

/* Check if packet is a fragment. */
uint32_t ipv4_is_fragment(struct ipv4_header *ip) {
    if ((ip->flags & 0x01) != 0) {
        return 1;
    }
    if (ip->frag_offset != 0) {
        return 1;
    }
    return 0;
}

/* Check if "don't fragment" flag is set. */
uint32_t ipv4_is_dont_fragment(struct ipv4_header *ip) {
    if ((ip->flags & 0x02) != 0) {
        return 1;
    }
    return 0;
}

/* Get payload size. */
uint32_t ipv4_payload_size(struct ipv4_header *ip) {
    uint32_t hdr_len;
    hdr_len = ip->ihl * 4;
    if (ip->total_length < hdr_len) {
        return 0;
    }
    return ip->total_length - hdr_len;
}

/* Check if protocol is TCP (6). */
uint32_t ipv4_is_tcp(struct ipv4_header *ip) {
    if (ip->protocol == 6) {
        return 1;
    }
    return 0;
}

/* Check if protocol is UDP (17). */
uint32_t ipv4_is_udp(struct ipv4_header *ip) {
    if (ip->protocol == 17) {
        return 1;
    }
    return 0;
}

/* Count bytes in buffer by traversal. */
uint32_t pkt_count_bytes(struct pkt_buffer *buf) {
    struct pkt_byte *cur;
    uint32_t count;
    count = 0;
    cur = buf->data;
    while (cur != NULL) {
        count = count + 1;
        cur = cur->next;
    }
    return count;
}

/* Validate buffer integrity: traversal count matches length field. */
uint32_t pkt_check_integrity(struct pkt_buffer *buf) {
    uint32_t actual;
    actual = pkt_count_bytes(buf);
    if (actual != buf->length) {
        return 0;
    }
    if (buf->length == 0) {
        if (buf->data != NULL) {
            return 0;
        }
    }
    return 1;
}
