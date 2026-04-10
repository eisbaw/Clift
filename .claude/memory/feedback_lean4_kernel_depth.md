---
name: Lean 4 kernel depth workaround for L1 proofs
description: When proving validHoare for L1 monadic computations over CState, mark hVal/heapUpdate as [local irreducible] and use simp projection lemmas to prevent kernel deep recursion
type: feedback
---

When proving `validHoare` for L1 monadic computations that modify heap state (via `hVal`/`heapUpdate`), the Lean 4 kernel hits a hardcoded recursion depth limit.

**Why:** The kernel tries to unfold `heapPtrValid (f s).globals.rawHeap ...` which goes through `hVal -> MemType.fromMem -> UInt32.fromBytes' -> assembleByte -> BitVec -> Nat div/mod`, exceeding ~512 depth.

**How to apply:**
1. Define step functions with anonymous constructors `⟨s.globals, ⟨...⟩⟩`, not `{ s with ... }`
2. `attribute [local irreducible] hVal heapUpdate` before the proof
3. Prove `@[simp]` projection lemmas for each step function (e.g., `swap_f1_globals : (swap_f1 s).globals = s.globals := rfl`)
4. Use `simp only [projection_lemmas]` BEFORE `heapPtrValid` reasoning
5. Chain `L1_guard_modify_result` / `L1_seq_singleton_ok` / `L1_catch_singleton_ok`

This was discovered after 5 failed approaches over multiple sessions. See task-0063 for full history.
