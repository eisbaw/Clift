# ADR-005: Stuck Outcome Merged Into Fault

## Status

Accepted

## Context

Schirmer's Simpl framework (Isabelle/HOL) uses four execution outcomes:
- `Normal s` — command completed normally
- `Abrupt s` — non-local control flow (throw, break, return)
- `Fault f` — guard violation (UB), parameterized by fault set `f`
- `Stuck` — undefined behavior from missing procedure body or spec failure

Our `Outcome` type has three constructors, merging Stuck into `fault`:
- `normal s`
- `abrupt s`
- `fault`

The question is whether to add a separate `stuck` constructor.

## Decision

**Keep the merged design: Stuck is subsumed by `fault`.**

Rationale:

1. **Both represent undefined behavior.** In C semantics, calling an
   undefined function and violating a guard both produce undefined
   behavior. The distinction in Simpl exists for Isabelle/HOL proof
   engineering reasons (separating "guard-triggered" from
   "semantically stuck"), not because C distinguishes them.

2. **Simpler proofs.** With three outcomes instead of four, every
   case split in `Exec` induction and Hoare rule proofs has one fewer
   case. This compounds across the entire pipeline.

3. **No loss of soundness.** The key property we need is: if a
   guard fails, the outcome is `fault` (not `normal`). Merging Stuck
   into fault preserves this — both are "bad" outcomes that Hoare
   triples must rule out.

4. **We don't model partial procedure environments.** In Simpl,
   `Stuck` arises when a procedure name is not in the environment.
   Our `ProcEnv` is total (every called procedure must have a body
   at import time). The CImporter rejects calls to undefined
   functions. So the primary source of Stuck does not arise.

5. **No `spec` nondeterministic failure yet.** The other Stuck source
   in Simpl is when a `spec` relation has no matching state. We use
   `spec` minimally and could model this as fault without ambiguity.

## Consequences

- `Outcome` stays at 3 constructors: `normal`, `abrupt`, `fault`.
- If we later need to distinguish guard-fault from stuck-fault
  (e.g., for better error reporting in counterexample generation),
  we can add a `stuck` constructor then. The change is localized
  to `Outcome`, `Exec`, and Hoare rule proofs.
- Code comment added to `Outcome.lean` documenting this decision.

## Alternatives Considered

- **Add `stuck` constructor**: Closer to Simpl, enables finer-grained
  reasoning about failure modes. Cost: every Exec rule and Hoare
  theorem needs an additional case. Not justified given our total
  ProcEnv design.
- **Parameterize `fault` with a tag**: See ADR-006 (deferred). Would
  allow distinguishing fault sources without adding a constructor.
