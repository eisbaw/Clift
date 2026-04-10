/* sha256_core.c -- Realistic SHA-256 compression function
 *
 * Faithfully represents mbedTLS/OpenSSL SHA-256 patterns:
 * - State as 8 x uint32_t hash values (H0-H7)
 * - Message schedule expansion (W array simulated with struct)
 * - 64-round compression with Ch, Maj, Sigma functions
 * - Bitwise heavy: right-rotate, shift, xor, and, or
 *
 * Constraints (CImporter subset):
 *   - No arrays: use structs with numbered fields
 *   - No floating point, goto, longjmp, VLAs
 *   - No pointer-to-pointer
 */

#include <stdint.h>
#include <stddef.h>

/* ================================================================
 * Data structures
 * ================================================================ */

/* SHA-256 state: 8 hash values */
struct sha256_state {
    uint32_t h0;
    uint32_t h1;
    uint32_t h2;
    uint32_t h3;
    uint32_t h4;
    uint32_t h5;
    uint32_t h6;
    uint32_t h7;
    uint32_t total_bytes;   /* Total bytes processed */
};

/* A single 512-bit message block (16 x uint32_t words) */
struct sha256_block {
    uint32_t w0;
    uint32_t w1;
    uint32_t w2;
    uint32_t w3;
    uint32_t w4;
    uint32_t w5;
    uint32_t w6;
    uint32_t w7;
    uint32_t w8;
    uint32_t w9;
    uint32_t w10;
    uint32_t w11;
    uint32_t w12;
    uint32_t w13;
    uint32_t w14;
    uint32_t w15;
};

/* Working variables for a compression round */
struct sha256_round {
    uint32_t a;
    uint32_t b;
    uint32_t c;
    uint32_t d;
    uint32_t e;
    uint32_t f;
    uint32_t g;
    uint32_t h;
};

/* ================================================================
 * Bitwise helper functions (SHA-256 building blocks)
 * ================================================================ */

/* Right-rotate a 32-bit value by n positions.
 * ROTR(x, n) = (x >> n) | (x << (32 - n)) */
uint32_t sha256_rotr(uint32_t x, uint32_t n) {
    return (x >> n) | (x << (32 - n));
}

/* SHA-256 Ch function: Ch(e, f, g) = (e AND f) XOR (NOT e AND g) */
uint32_t sha256_ch(uint32_t e, uint32_t f, uint32_t g) {
    return (e & f) ^ ((~e) & g);
}

/* SHA-256 Maj function: Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c) */
uint32_t sha256_maj(uint32_t a, uint32_t b, uint32_t c) {
    return (a & b) ^ (a & c) ^ (b & c);
}

/* SHA-256 big sigma 0: SIGMA0(a) = ROTR(a,2) XOR ROTR(a,13) XOR ROTR(a,22) */
uint32_t sha256_bsigma0(uint32_t a) {
    uint32_t r2;
    uint32_t r13;
    uint32_t r22;
    r2 = sha256_rotr(a, 2);
    r13 = sha256_rotr(a, 13);
    r22 = sha256_rotr(a, 22);
    return r2 ^ r13 ^ r22;
}

/* SHA-256 big sigma 1: SIGMA1(e) = ROTR(e,6) XOR ROTR(e,11) XOR ROTR(e,25) */
uint32_t sha256_bsigma1(uint32_t e) {
    uint32_t r6;
    uint32_t r11;
    uint32_t r25;
    r6 = sha256_rotr(e, 6);
    r11 = sha256_rotr(e, 11);
    r25 = sha256_rotr(e, 25);
    return r6 ^ r11 ^ r25;
}

/* SHA-256 small sigma 0: sigma0(x) = ROTR(x,7) XOR ROTR(x,18) XOR (x >> 3) */
uint32_t sha256_ssigma0(uint32_t x) {
    uint32_t r7;
    uint32_t r18;
    uint32_t s3;
    r7 = sha256_rotr(x, 7);
    r18 = sha256_rotr(x, 18);
    s3 = x >> 3;
    return r7 ^ r18 ^ s3;
}

/* SHA-256 small sigma 1: sigma1(x) = ROTR(x,17) XOR ROTR(x,19) XOR (x >> 10) */
uint32_t sha256_ssigma1(uint32_t x) {
    uint32_t r17;
    uint32_t r19;
    uint32_t s10;
    r17 = sha256_rotr(x, 17);
    r19 = sha256_rotr(x, 19);
    s10 = x >> 10;
    return r17 ^ r19 ^ s10;
}

/* ================================================================
 * Initialization
 * ================================================================ */

/* Initialize SHA-256 state with standard IV (FIPS 180-4 section 5.3.3). */
void sha256_init(struct sha256_state *st) {
    st->h0 = 0x6a09e667;
    st->h1 = 0xbb67ae85;
    st->h2 = 0x3c6ef372;
    st->h3 = 0xa54ff53a;
    st->h4 = 0x510e527f;
    st->h5 = 0x9b05688c;
    st->h6 = 0x1f83d9ab;
    st->h7 = 0x5be0cd19;
    st->total_bytes = 0;
}

/* Initialize round working variables from current hash state. */
void sha256_round_init(struct sha256_round *r, struct sha256_state *st) {
    r->a = st->h0;
    r->b = st->h1;
    r->c = st->h2;
    r->d = st->h3;
    r->e = st->h4;
    r->f = st->h5;
    r->g = st->h6;
    r->h = st->h7;
}

/* ================================================================
 * Single compression round
 * ================================================================ */

/* Execute one SHA-256 compression round.
 * T1 = h + SIGMA1(e) + Ch(e,f,g) + k + w
 * T2 = SIGMA0(a) + Maj(a,b,c)
 * Then rotate: h=g, g=f, f=e, e=d+T1, d=c, c=b, b=a, a=T1+T2 */
void sha256_round_step(struct sha256_round *r, uint32_t k, uint32_t w) {
    uint32_t s1;
    uint32_t ch;
    uint32_t t1;
    uint32_t s0;
    uint32_t maj;
    uint32_t t2;

    s1 = sha256_bsigma1(r->e);
    ch = sha256_ch(r->e, r->f, r->g);
    t1 = r->h + s1 + ch + k + w;

    s0 = sha256_bsigma0(r->a);
    maj = sha256_maj(r->a, r->b, r->c);
    t2 = s0 + maj;

    r->h = r->g;
    r->g = r->f;
    r->f = r->e;
    r->e = r->d + t1;
    r->d = r->c;
    r->c = r->b;
    r->b = r->a;
    r->a = t1 + t2;
}

/* ================================================================
 * Finalize: add round result back to hash state
 * ================================================================ */

/* Add the working variables back to the hash state (step 4 of compression). */
void sha256_round_finalize(struct sha256_state *st, struct sha256_round *r) {
    st->h0 = st->h0 + r->a;
    st->h1 = st->h1 + r->b;
    st->h2 = st->h2 + r->c;
    st->h3 = st->h3 + r->d;
    st->h4 = st->h4 + r->e;
    st->h5 = st->h5 + r->f;
    st->h6 = st->h6 + r->g;
    st->h7 = st->h7 + r->h;
    st->total_bytes = st->total_bytes + 64;
}

/* ================================================================
 * Message schedule helpers
 * (Normally this would be a loop over W[0..63], but without arrays
 *  we demonstrate the pattern for the first few schedule entries.)
 * ================================================================ */

/* Compute a message schedule word: W[t] = sigma1(W[t-2]) + W[t-7] + sigma0(W[t-15]) + W[t-16]
 * This is a generic helper that takes the 4 input words. */
uint32_t sha256_schedule_word(uint32_t w_t_2, uint32_t w_t_7,
                              uint32_t w_t_15, uint32_t w_t_16) {
    uint32_t s0;
    uint32_t s1;
    s1 = sha256_ssigma1(w_t_2);
    s0 = sha256_ssigma0(w_t_15);
    return s1 + w_t_7 + s0 + w_t_16;
}

/* ================================================================
 * Utility: check if state matches expected IV
 * ================================================================ */

/* Verify the state matches the standard SHA-256 IV. Returns 1 if match. */
uint32_t sha256_check_iv(struct sha256_state *st) {
    if (st->h0 != 0x6a09e667) { return 0; }
    if (st->h1 != 0xbb67ae85) { return 0; }
    if (st->h2 != 0x3c6ef372) { return 0; }
    if (st->h3 != 0xa54ff53a) { return 0; }
    if (st->h4 != 0x510e527f) { return 0; }
    if (st->h5 != 0x9b05688c) { return 0; }
    if (st->h6 != 0x1f83d9ab) { return 0; }
    if (st->h7 != 0x5be0cd19) { return 0; }
    return 1;
}

/* Compare two SHA-256 states for equality. Returns 1 if equal. */
uint32_t sha256_state_equal(struct sha256_state *a, struct sha256_state *b) {
    if (a->h0 != b->h0) { return 0; }
    if (a->h1 != b->h1) { return 0; }
    if (a->h2 != b->h2) { return 0; }
    if (a->h3 != b->h3) { return 0; }
    if (a->h4 != b->h4) { return 0; }
    if (a->h5 != b->h5) { return 0; }
    if (a->h6 != b->h6) { return 0; }
    if (a->h7 != b->h7) { return 0; }
    return 1;
}
