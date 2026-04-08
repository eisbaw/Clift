# ADR-001: L1 Exception Encoding

## Status
Accepted

## Context
The L1 lifting stage (SimplConv) converts CSimpl deeply-embedded commands into
a shallow monadic embedding. CSimpl has three outcome types:
- `Outcome.normal s` -- normal completion
- `Outcome.abrupt s` -- non-local control flow (throw/return/break)
- `Outcome.fault`    -- undefined behavior (guard violation)

We need to choose how to encode these three outcomes in the L1 monad type,
which is built on top of our existing `NondetM σ α` (nondeterministic state
monad with failure flag).

## Decision
**L1Monad σ := NondetM σ (Except Unit Unit)**

The encoding is:
- Normal outcome `Outcome.normal s` -> `(Except.ok (), s')` in results
- Abrupt outcome `Outcome.abrupt s` -> `(Except.error (), s')` in results
- Fault `Outcome.fault` -> `NondetM` failure flag (failed = True)

This means:
- The return type is `Except Unit Unit` -- `ok ()` for normal, `error ()` for abrupt
- Fault maps to the monad's built-in failure mechanism
- Both Unit types because CSimpl doesn't carry typed return values at L1;
  the return value is stored in a state field (ret__val)

## Rationale

### Why Except Unit Unit?
seL4's AutoCorres uses `(unit, unit, 's) exn_monad` for L1 -- an exception
monad where both the result type and the exception type are unit. This is
because at L1, the state carries all information (including return values
via `ret__val`). The Except encoding is purely for control flow signaling.

### Why fault -> NondetM failure?
NondetM already has a failure flag. Guard violations (UB) are exactly the
failure condition this flag is designed for. Using the existing mechanism
avoids adding a third sum case and keeps the encoding minimal.

### Why not modify NondetM?
The plan says "Do NOT modify NondetM itself." NondetM is a general-purpose
nondeterministic state monad. The L1 exception encoding is specific to the
C lifting pipeline. Encoding it in the return type keeps NondetM clean and
reusable.

### Alternatives considered
1. **Three-case sum type**: `Inductive L1Result | normal | abrupt | fault`.
   Rejected: duplicates NondetM's failure mechanism for fault.
2. **Option (Except Unit Unit)**: Using None for fault. Rejected: NondetM
   failure is more natural and already has proof infrastructure.
3. **Separate abrupt flag in NondetResult**: Would require modifying NondetM.
   Rejected per plan constraints.

## Consequences
- L1corres must map Exec outcomes to the appropriate Except/failure encoding
- L1 combinators (L1_seq, L1_catch, etc.) operate on `NondetM σ (Except Unit Unit)`
- L2 (LocalVarExtract) will change the return type when extracting locals
- Proof infrastructure for `Except` is needed (catch/throw monadic operations)
