# ADR-004: Address Space Model (memSize = 2^32)

## Status

Accepted

## Context

Our memory model uses `memSize : Nat := 2^32` as the address space size.
However, `Ptr α` stores addresses as 8-byte values (UInt64 encoding via
`Ptr.toBytes'`/`Ptr.fromBytes'`). On real x86-64 LP64, addresses are 64-bit.
On ARM embedded, 32-bit.

The inconsistency: `Ptr.fromBytes'` decodes an 8-byte address then takes
`% memSize`, silently truncating addresses above 2^32. This is technically
sound (the modular arithmetic is well-defined), but could mask bugs where
a 64-bit address is truncated.

## Decision

**Keep memSize = 2^32 for now.** Rationale:

1. **Proof ergonomics**: memSize = 2^32 keeps `omega` proofs tractable.
   With memSize = 2^64, address arithmetic proofs would involve 64-bit
   constants that stress omega and kernel checking.

2. **Sufficient for target use case**: Our current targets (embedded C,
   small programs) use addresses well within 32-bit range. The address
   space size is a parameter of the model, not the real hardware.

3. **The truncation is guarded**: `heapPtrValid` requires
   `p.addr.val + size <= memSize`, so any valid pointer is within range.
   The truncation in `Ptr.fromBytes'` only affects addresses that would
   fail the validity check anyway.

4. **Future-proof path**: When we need 64-bit address support, change
   `memSize` to `2^48` (canonical x86-64 address space) or `2^64`.
   All proofs are parametric over `memSize` through the constant, so
   the change is localized. The main cost will be re-checking omega proofs.

## Consequences

- Pointer encoding uses 8 bytes (matching LP64 ABI) but the effective
  address space is 32-bit. This is internally consistent because
  `Ptr.fromBytes'` applies `% memSize`.
- All heap operations (read, write, validity) are bounded by memSize.
- When scaling to real x86-64 programs, memSize must be increased and
  proofs re-checked.

## Alternatives Considered

- **memSize = 2^64**: Correct for LP64 but omega proofs with 2^64
  constants are significantly slower. Not worth the cost at this stage.
- **memSize = 2^48**: x86-64 canonical address space. Better match but
  still larger than needed for our test programs.
- **Parametric memSize**: Make memSize a typeclass parameter or universe
  variable. Adds complexity to every type and proof for no current benefit.
