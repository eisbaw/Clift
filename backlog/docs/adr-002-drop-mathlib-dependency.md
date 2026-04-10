# ADR-002: Drop Mathlib Dependency

## Status
Accepted

## Date
2026-04-08

## Context

The project imported Mathlib for two things:
- `Mathlib.Data.Set.Basic` in `Clift/MonadLib/NondetM.lean` -- providing `Set α`, membership, singleton, set-builder notation, union, extensionality
- `Mathlib.Data.Fin.Basic` in `Clift/CSemantics/State.lean` -- providing `UInt32.ext` (UInt32 extensionality)

Mathlib causes 9GB+ RAM per Lean process, making development impractical on most machines. The dependency was pulling in 500+ transitive modules for ~15 lemmas actually used.

## Decision

Drop Mathlib entirely and replace with minimal local definitions:

1. **`Clift/Util/SetBasic.lean`**: Defines `Set α := α → Prop` (as `abbrev` for kernel reducibility), plus `Membership`, `EmptyCollection`, `Singleton`, `Insert`, `Union`, `Set.ext`, `Set.mem_union_left`, `Set.mem_union_right`. About 70 lines total.

2. **`Clift/Util/UInt32Ext.lean`**: Proves `UInt32.ext` (if `a.toNat = b.toNat` then `a = b`) using `BitVec.eq_of_toNat_eq`. 5 lines.

3. **Set-builder notation `{x | p x}`**: Replaced with explicit lambdas `(fun x => p x)` since `Set α` is an `abbrev` for `α → Prop`, so these are interchangeable.

4. **Mathlib tactics**: `by_contra` replaced with `by_cases`/`exfalso`, `conv_lhs` replaced with `conv => lhs`, `not_not` replaced with `Decidable.not_not`, `le_refl` replaced with `Nat.le_refl`.

## Consequences

### Positive
- Build uses <500MB RAM instead of 9GB+
- Clean build takes ~30s instead of 10+ minutes
- No dependency on Mathlib version pinning
- `lake-manifest.json` eliminated (was pinning Mathlib commit)

### Negative
- Must maintain our own Set lemmas (currently ~70 lines, unlikely to grow much)
- If we later need Mathlib's BitVec/omega lemmas heavily (Phase 2 WordAbstract), we may need to re-evaluate
- Some Lean 4 community tactics (`by_contra`, `conv_lhs`) are not available without Std/Mathlib

### Neutral
- The `sorry` in `Examples/SwapProof.lean` (`l1_swap_validHoare`) was NOT caused by Mathlib removal -- it's a pre-existing kernel deep recursion issue with nested `{ s with ... }` structure updates

## Risks
- If Lean 4 changes the `Membership` class signature again (it changed between versions -- container-first vs element-first), our SetBasic.lean will break. Mitigation: pinned lean-toolchain.
- If we need more Set/Fin lemmas, we add them to Util/ rather than re-importing Mathlib.

## Re-evaluation (2026-04-08, Task 0114)

### Context
Task-0105 (MetaM VCG) is partially done -- the tactic shell exists but full
automatic weakest precondition computation is deferred. Task-0112 (Claude
benchmark) measured 85% first-attempt success, 100% with retries, on 20
proof obligations WITHOUT Mathlib.

### Analysis of the 15% failure cases
Claude's failures were in 3 categories:
1. **Set extensionality idioms** (3 goals): Needed `change (_ or _)` + `rcases`
   for NondetM result sets. Our custom `SetBasic.lean` handles this. Mathlib
   would provide the same `Set.ext` -- no advantage.
2. **Irreducibility hints** (1 goal): Knowing to mark `hVal`/`heapUpdate`
   as `[local irreducible]` before structure projection proofs. This is
   entirely Clift-domain knowledge. Mathlib has zero relevance.
3. **Deep CSimpl constructor names** (1 goal): Guessing `Exec.seqNormal` vs
   `Exec.seqAbrupt` etc. These are our own inductives. Mathlib irrelevant.

### Remaining proof effort categorization
After MetaM VCG automates L1 stepping, the remaining manual proof effort is:
- ~50% heap/pointer reasoning (separation logic, frame rule)
- ~25% loop invariant proofs (induction, termination)
- ~15% abstract spec reasoning (List, Nat arithmetic)
- ~10% set/NondetM internals

Mathlib could help with the 15% abstract spec reasoning (List lemmas, Nat
facts). But `omega` handles most Nat goals, and `List` lemmas are simple
enough to prove inline. The 50% heap reasoning is entirely Clift-specific.

### Decision: KEEP OUT permanently

Rationale:
1. Claude's failure patterns are Clift-domain-specific, not math-library gaps
2. 85% -> 100% with retries means patterns can be learned, not library-provided
3. RAM savings (500MB vs 9GB+) are critical for developer experience
4. Build time savings (25s vs 10min+) compound over hundreds of builds
5. The remaining 15% abstract spec reasoning is better served by targeted
   lemmas in Util/ than importing 500+ Mathlib modules
6. At 81 functions, zero proof obligations have required Mathlib lemmas

### What to do instead
- Add specific lemmas to `Clift/Util/` as needed (List.length_append, etc.)
- Document Clift-specific proof patterns for Claude context
- Invest in MetaM VCG completion rather than Mathlib import
