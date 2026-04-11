# Second Verification Campaign: Assessment

Task 0212: Assessment of verifying a second C module end-to-end.

## Purpose

Verify a second module to demonstrate Clift is general, not ring-buffer-specific.

## Module Selection Criteria

1. Different domain from ring buffer (not a linked-list data structure)
2. Moderate complexity (10-20 functions, <500 LOC)
3. Mix of simple accessors and complex operations
4. No features Clift doesn't support (no arrays, function pointers, etc.)

## Candidate Modules

### A. SHA-256 Core (sha256_core.c)
- Already imported (Generated/Sha256Core.lean exists)
- 8 functions, ~200 LOC
- Mix: pure bitwise operations + loop-based compression
- Challenge: bitwise operations need UInt32 lemma support
- Estimated effort: 3-5 days for full verification
- **Recommended**: different domain (crypto), tests bitwise support

### B. UART Driver (uart_driver.c)
- Already imported (Generated/UartDriver.lean exists)
- 6 functions, ~150 LOC
- Hardware register read/write pattern
- Challenge: heap mutations at register addresses
- Estimated effort: 2-3 days
- Good for I/O-style verification

### C. Packet Parser (packet_parser.c)
- Already imported (Generated/PacketParser.lean exists)
- 10 functions, ~300 LOC
- Nested struct access, error code propagation
- Challenge: multi-level pointer dereferences
- Estimated effort: 4-6 days
- Good for security-critical code verification

### D. RTOS Queue (rtos_queue.c)
- Already imported (Generated/RtosQueue.lean exists)
- 8 functions, ~250 LOC
- Similar domain to ring buffer (queue) but different implementation
- Estimated effort: 3-4 days
- Less valuable: too similar to ring buffer

## Recommendation

**SHA-256 Core** is the best second target because:
1. Completely different domain (crypto vs. data structure)
2. Pure bitwise functions test a different proof pattern
3. Small enough to be feasible
4. Verifying crypto code has high practical value
5. Good comparison point: how does Clift handle math-heavy code?

## Verification Plan for SHA-256

1. **FuncSpecs** (1 day): Define specs for all 8 functions
   - sha256_ch, sha256_maj, sha256_sigma0/1, sha256_gamma0/1
   - sha256_init, sha256_compress_block
2. **Simple function proofs** (1 day): ch, maj, sigma, gamma
   - These are pure bitwise: guard-modify-throw pattern
   - Should follow the same pattern as rb_capacity
3. **init proof** (0.5 day): multi-field heap write
   - Same pattern as rb_init
4. **compress_block proof** (2-3 days): the hard one
   - 64-round loop with complex state updates
   - Needs loop invariant + UInt32 arithmetic lemmas
5. **Refinement** (1 day): abstract spec + simulation relation

## What Would Be Verified

- Functional correctness of each function against its spec
- No undefined behavior (totalHoare for non-loop functions)
- Refinement from abstract SHA-256 spec to C implementation

## Risks

- UInt32 bitwise lemma gaps in Lean's standard library
- The compress loop (64 rounds) may be too complex for automated proof
- May need to extend CImporter for bitwise expression support
