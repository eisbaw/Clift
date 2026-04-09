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
