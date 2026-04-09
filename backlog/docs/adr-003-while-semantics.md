# ADR-003: Inductive WhileResult/WhileFail vs Fin-indexed State Chains

## Status
Accepted

## Date
2026-04-08

## Context

The NondetM monad needs a `whileLoop` combinator to serve as the monadic
equivalent of `CSimpl.while`. A while loop can produce results (final states
after the loop terminates) and can fail (if the body fails during some
iteration). We needed to decide how to characterize these sets.

Two approaches were considered:

1. **Fin-indexed state chains**: Define a chain of `n` states `s₀, s₁, ..., sₙ`
   where each step satisfies the body relation. Results are states reachable
   via some finite chain. Failure occurs when some chain prefix leads to a
   failing body state.

2. **Inductive predicates**: Define `WhileResult c body s s'` and
   `WhileFail c body s` as inductive types with base cases and step cases.

## Decision

**Use inductive predicates (WhileResult / WhileFail).**

Both NondetM and L1 define their own versions:

- `NondetM.WhileResult c body s s'`: state `s'` is reachable from `s` by
  iterating `body` while `c` holds, then `c` becomes false.
- `NondetM.WhileFail c body s`: failure is reachable from `s` by iterating
  `body` while `c` holds, with the body failing at some iteration.
- `L1.WhileResult c body s p`: like NondetM's but tracks `Except Unit Unit`
  return values, with an additional `abrupt` case for early exit via throw.
- `L1.WhileFail c body s`: same structure, failure reachable through ok-steps.

## Rationale

### Why inductive predicates beat Fin-indexed chains

The Fin-indexed approach was attempted first and abandoned. The problems:

1. **Existential quantification over chain length**: Every result statement
   requires `exists n, exists chain : Fin (n+1) -> sigma, ...`. This adds
   an extra layer of quantifiers to every proof goal, making tactics heavier.

2. **Induction is unnatural**: Induction over `Fin n` requires careful index
   arithmetic. The step case gives you a chain of length `n+1` and you need
   to split it into a prefix of length `n` plus one step, which requires
   auxiliary lemmas about `Fin` manipulation.

3. **The hoare_while proof was dramatically harder**: The while-loop Hoare rule
   (`validHoare (fun s => P s /\ c s = true) body (fun _ => P)` implies
   `validHoare P (whileLoop c body) (fun _ s => P s /\ c s = false)`)
   required multiple pages of Fin arithmetic with the chain approach.
   With inductive predicates, it's a clean structural induction.

4. **L1corres_while induction**: The correspondence proof for while loops
   does induction on the `Exec` derivation. The inductive hypothesis
   naturally produces `WhileResult` constructors. With Fin-indexed chains,
   you'd need to construct chains incrementally, managing indices.

### Why the inductive approach works well

- **Structural induction**: `WhileResult.step` gives exactly the right
  induction principle. The recursive case hands you `WhileResult c body t s'`
  for the tail, which is the induction hypothesis.
- **Clean base cases**: `WhileResult.done` for when the condition is false.
  `WhileFail.here` for immediate failure. No index arithmetic.
- **Direct construction in proofs**: When proving a state is in the result set,
  you build a `WhileResult` derivation step by step, which reads naturally.
- **Mirrors Exec**: The `Exec` big-step semantics for while uses the same
  inductive pattern (whileTrue chains to whileFalse). The WhileResult
  predicate mirrors this structure, making L1corres proofs natural.

### Limitation

The inductive definition gives a least fixed point. This means non-terminating
loops have an empty result set (no WhileResult derivation exists for an
infinite chain). This is correct for partial correctness semantics -- a
non-terminating loop satisfies any postcondition vacuously. Total correctness
requires a separate termination argument (a decreasing measure), which is
handled by `totalHoare` requiring `results.Nonempty`.

## Consequences

- `NondetM.whileLoop` is defined using `WhileResult` and `WhileFail`
- `L1.while` extends this with an `abrupt` case for exception support
- All while-related proofs (Hoare rules, L1corres) use structural induction
  on these predicates
- The same pattern should be used for any future loop constructs (do-while,
  for-loops) if they are added to CSimpl
