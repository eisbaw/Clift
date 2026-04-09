# ADR-006: Guard Fault-Set Parameter Deferred

## Status

Accepted (deferred to Phase 4+)

## Context

In Schirmer's Simpl, the `Guard` constructor has a fault-set parameter:

```
Guard f g c    -- if g holds, execute c; else Fault f
```

where `f` is a set of "fault tags" identifying which guard failed. This
allows Hoare triples to be parameterized by which faults are tolerated,
enabling proofs that say "this program is free of overflow faults but may
have null-pointer faults."

Our `CSimpl.guard` has only the predicate:

```lean
| guard : (sigma -> Prop) -> CSimpl sigma -> CSimpl sigma
```

The fault outcome carries no identifying information.

## Decision

**Defer the fault-set parameter. Not needed for current phases.**

Rationale:

1. **Soundness is unaffected.** Guard correctness requires proving
   the guard predicate holds (ruling out fault). Whether the fault
   carries a tag does not affect whether the proof obligation is
   discharged.

2. **Current proofs don't need it.** Our Hoare triples prove total
   absence of faults (the `nf` / no-fail flags in `corres`). We
   don't need to selectively tolerate some fault classes while
   ruling out others.

3. **Adding it later is straightforward.** The change is:
   - Add a type parameter `F` to `CSimpl` (or a `FaultTag` field to `guard`)
   - Change `fault` in `Outcome` to `fault : F -> Outcome sigma`
   - Update `Exec` rules: `guardFault` carries the tag
   - Update Hoare rules to be parametric in tolerated fault sets

   This is mechanical but touches many files. Better to do it when
   there's a concrete use case (Phase 4 automation / error reporting).

4. **Phase 4 automation is the right time.** When building `c_vcg`
   and counterexample generation, fault tags become useful for
   reporting *which* guard failed. That is when the cost of adding
   the parameter pays off.

## Consequences

- `CSimpl.guard` stays as `(sigma -> Prop) -> CSimpl sigma -> CSimpl sigma`.
- `Outcome.fault` carries no data.
- When fault-set support is needed, it will require updating `CSimpl`,
  `Outcome`, `Exec`, and all Hoare/corres rules. Estimated cost:
  1-2 days of mechanical changes.
- Code comment added to `CSimpl.lean` noting this design choice.

## Alternatives Considered

- **Add fault-set now**: Would match Simpl exactly but adds complexity
  to every proof for no current benefit. Every `Exec` case analysis
  and `corres` lemma would need to thread through the fault-set type.
- **Use a global fault tag type**: Fix a single `FaultTag` inductive
  rather than parameterizing. Simpler than the full Simpl approach but
  still adds a field to `guard` and `fault`. Same "not needed yet" argument.
