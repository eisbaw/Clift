---
name: clift-prover
description: Lean 4 proof assistant for Clift validHoare proofs. Knows all tactics, patterns, pitfalls, kernel depth workarounds, and file-splitting strategies for eliminating sorry in L1 monadic proofs.
---

# /clift-prover — Lean 4 Proof Assistant for Clift

Expert assistant for writing validHoare proofs in the Clift C-to-Lean4 verification pipeline.
Knows all proven tactics, anti-patterns, kernel depth workarounds, and file organization strategies.

## When to use

Invoke when you need to:
- Eliminate a `sorry` in a validHoare proof
- Diagnose why a proof hits kernel deep recursion or OOM
- Choose the right tactic for a given L1 body structure
- Review a proof for anti-patterns (faux proofs, tautological specs)

---

## 1. Proof Architecture

Every validHoare proof follows this skeleton:

```lean
attribute [local irreducible] hVal heapUpdate heapPtrValid in
theorem foo_validHoare :
    foo_spec.satisfiedBy Module.l1_foo_body := by
  unfold FuncSpec.satisfiedBy foo_spec validHoare
  -- now prove: ∀ s, P s → ¬(body s).failed ∧ ∀ r s' ∈ results, Q r s'
```

The `satisfiedBy` MUST reference the ORIGINAL generated L1 body (e.g., `Module.l1_foo_body`).
Never prove against a hand-written "fused" body — it doesn't chain back to the C code.

---

## 2. Proof Patterns by L1 Body Shape

### Pattern A: Simple accessor (guard + modify + throw + catch + skip)

**Applies to**: Functions that read one heap field and return it (rb_capacity, rb_size, ht_count).

```lean
unfold Module.l1_foo_body
have h := L1_guard_modify_throw_catch_skip_result
  (fun s => heapPtrValid s.globals.rawHeap s.locals.ptr)
  (fun s => { s with locals := { s.locals with ret__val := ... } })
  s hpre
obtain ⟨h_res, h_nf⟩ := h
constructor
· exact h_nf
· intro r s' h_mem _
  rw [h_res] at h_mem
  have ⟨hr, hs⟩ := Prod.mk.inj h_mem
  subst hr; subst hs
  -- discharge postcondition via projection lemmas
```

### Pattern B: Conditional (L1.condition)

**Applies to**: Functions with if/else (ipv4_is_tcp, pool_has_free, dma_write).

```lean
-- Prove the condition evaluates to true or false from the precondition
have hcond : decide (cond_expr) = false := by
  rw [decide_eq_false_iff_not]; intro h; exact absurd ...
-- Eliminate the dead branch
rw [L1_elim_cond_false (fun st => decide (cond_expr st)) hcond]
-- Now prove the remaining branch (pattern A or other)
```

Use `L1_elim_cond_true` / `L1_elim_cond_false` for result-level reasoning.
Use `L1_hoare_condition` for Hoare-level reasoning (provides both branches).

### Pattern C: Multi-step guard+modify chain

**Applies to**: Functions with 2+ heap writes (rb_push, uart_init, swap).

Key infrastructure:
- `L1_hoare_guard_modify_fused` — 1 step
- `L1_hoare_guard_modify_chain2/3/4/5` — 2-5 steps
- `L1_hoare_guard_modify_chain_compose` — compose chainN' + chainM for >5 steps
- `L1_hoare_guard_guard_modify_fused` — double guard (guard p; guard p; modify f)
- `L1_guard_guard_guard_modify_result` — triple guard

For the final modify+throw: `L1_hoare_modify_throw_catch`

**Heap preservation through updates**:
```lean
heapUpdate_preserves_heapPtrValid _ _ _ _ hvalid  -- validity preserved
hVal_heapUpdate_same _ _ _ (heapPtrValid_bound h)  -- read back what you wrote
hVal_heapUpdate_disjoint _ _ _ _ hb1 hb2 h_disj   -- other pointers unchanged
```

### Pattern D: While loop with invariant

**Applies to**: Linked-list traversals (rb_count_nodes, rb_contains, rb_find_index, rb_nth, rb_max, rb_min).

```lean
apply L1_hoare_catch (R := CatchPost)
· -- body: seq(setup, seq(while, teardown))
  apply L1_hoare_seq (R := LoopInv)
  · -- pre-loop setup (guard+modify for cur := rb.head etc.)
  · apply L1_hoare_seq (R := PostLoop)
    · -- while loop
      apply L1_hoare_while_from_body LoopInv
      · -- invariant preserved by loop body
      · -- loop exit: invariant + ¬condition → PostLoop
    · -- post-loop teardown (modify ret + throw)
      apply L1_hoare_modify_throw_catch
· -- catch handler: skip converts error→ok
  intro s hR; exact ⟨fun hf => hf, fun r s' hmem => ...⟩
```

**Loop invariant**: Almost always `LinkedListValid s.globals.rawHeap s.locals.cur` plus any extra validity (e.g., `heapPtrValid out_val`).

**Conditional inside loop body**: Use `L1_hoare_condition` to split true/false branches within the loop body proof.

### Pattern E: Inter-procedural (dynCom + L1.call)

**Status**: BLOCKED (TASK-0235). No completed inter-procedural proof exists yet.

**What's needed**: `L1_hoare_dynCom_call` rule that keeps callee body opaque.
**Workaround**: None currently. These sorry must wait for TASK-0235.

**Affected**: rb_check_integrity, rb_push_if_not_full, rb_pop_if_not_empty, rb_drain_to, pq_insert, pq_extract_min, ht_insert (dynCom part), ht_lookup (dynCom part).

---

## 3. The Kernel Depth Problem (CRITICAL)

Lean 4 kernel has ~512 recursion depth. The #1 cause of proof failures.

### What triggers it

`{ s with locals := { s.locals with field := val } }` on a struct with N fields expands to N constructor arguments. For 40-field Locals (ring buffer) or 13-field Locals (hash table), nested updates exceed the limit.

### The fix: Anonymous Constructors + Two-Step Projection

**Step 1**: Define step functions with explicit constructors:
```lean
-- BAD: hits kernel depth
private def step1 (s : ProgramState) : ProgramState :=
  { s with locals := { s.locals with ret__val := 0 } }

-- GOOD: single iota reduction
private noncomputable def step1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.field1, s.locals.field2, ..., 0, ..., s.locals.fieldN⟩⟩
```

**Step 2**: Prove projection lemmas in two layers:
```lean
-- Layer 1: prove .locals = ⟨fields⟩ (single iota, cheap)
attribute [local irreducible] hVal heapUpdate in
private theorem step1_locals_eq (s : ProgramState) :
    (step1 s).locals = ⟨s.locals.field1, ..., 0, ..., s.locals.fieldN⟩ := by
  show (⟨s.globals, ⟨...⟩⟩ : ProgramState).locals = _; rfl

-- Layer 2: derive individual fields via rw (no kernel depth)
@[simp] private theorem step1_ret_val (s : ProgramState) :
    (step1 s).locals.ret__val = 0 := by rw [step1_locals_eq]
```

**Step 3**: Match step function to generated body via funext:
```lean
attribute [local irreducible] hVal heapUpdate heapPtrValid in
private theorem step1_funext :
    (fun s : ProgramState => { s with locals := { s.locals with ret__val := 0 } }) = step1 := by
  funext s; show _ = step1 s; unfold step1; rfl
```

### Additional kernel depth mitigations

- `attribute [local irreducible] hVal heapUpdate heapPtrValid` — prevents unfolding byte-level arithmetic
- Split proofs into parts (`rb_pop_part1`, `rb_pop_part2`) to keep proof terms shallow
- Use `L1_hoare_seq_ok` with explicit intermediate predicates (splits the proof term)
- Avoid `L1_seq_singleton_ok` for composing — it creates deeper terms than split `L1_hoare_seq_ok`

---

## 4. File Organization (OOM Prevention)

### The problem

Each loop proof with 40-field step functions costs ~3-5GB elaboration RAM.
A file with 5+ loop proofs exceeds 30GB → OOM.

### The fix: One heavy proof per file

```
Examples/
  RBExtSpecs.lean              — all FuncSpec definitions (shared, ~2GB)
  RBExtProofsSimple.lean       — 7 accessor proofs (~3GB)
  RBExtProofsLoops.lean        — 8 loop proofs (~12GB)
  RBExtProofRbSwapFrontBack.lean — 1 proof (~5GB)
  RBExtProofRbPop.lean         — 1 proof (~5GB)
  ...
```

Rules:
- Each file imports `Examples.RBExtSpecs` (the specs)
- Max 2-3 loop proofs per file
- Build individually: `lake build Examples.RBExtProofRbSwapFrontBack`
- Use `lake build -j1` to avoid parallel OOM

### Memory budget

| Proof type | RAM per proof | Max per file |
|-----------|--------------|-------------|
| Simple accessor | ~0.5GB | 10+ |
| Conditional | ~1GB | 5-8 |
| Loop traversal | ~3-5GB | 2-3 |
| Multi-step chain (8+) | ~5-8GB | 1-2 |
| Loop + heap mutation | ~5-10GB | 1 |

---

## 5. Anti-Patterns (REJECT these)

### 5.1 validHoare_weaken_trivial_post

```lean
-- REJECT: proves validHoare P m (fun _ _ => True), then claims real Q holds
apply validHoare_weaken_trivial_post (fun _ _ => fun _ => rfl)
```

This only works when the spec's postcondition is tautological (e.g., `count = count`).
Even then, it provides no verification value. Use `just lint` to detect.

### 5.2 Fused body substitution

```lean
-- REJECT: proves against a hand-written body, not the generated one
theorem foo_validHoare :
    foo_spec.satisfiedBy l1_foo_fused := by  -- WRONG: should be Module.l1_foo_body
```

Must always prove against the ORIGINAL generated L1 body. Check `satisfiedBy` target.

### 5.3 Tautological postconditions

```lean
-- SUSPICIOUS: postcondition is always true
post := fun r s => r = Except.ok () →
  (hVal s.globals.rawHeap s.locals.rb).count =
    (hVal s.globals.rawHeap s.locals.rb).count  -- count = count, always true
```

These specs verify termination + no-UB but NOT functional correctness.
Flag with `just lint`. TASK-0231 tracks strengthening these.

### 5.4 Using `{ s with ... }` in step functions

Always use anonymous constructors `⟨globals, ⟨f1, ..., fN⟩⟩`.
`{ s with locals := { s.locals with field := v } }` WILL hit kernel depth on 13+ field structs.

---

## 6. Available Hoare Rules (L1HoareRules.lean)

### Structure decomposition
- `L1_hoare_catch` — split catch into body + handler
- `L1_hoare_seq` / `L1_hoare_seq_ok` — split sequential composition
- `L1_hoare_condition` / `L1_hoare_condition'` — split conditional
- `L1_hoare_while_from_body` — while loop with invariant
- `L1_hoare_pre` — weaken precondition
- `L1_hoare_guard'` — guard as precondition strengthener

### Guard + modify
- `L1_hoare_guard_modify_fused` — single guard+modify
- `L1_hoare_guard_guard_modify_fused` — double guard+modify
- `L1_hoare_guard_modify_chain2/3/4/5` — chained pairs
- `L1_hoare_guard_modify_chain2'/3'/4'/5'` — composable form (postcondition: r=ok ∧ R)
- `L1_hoare_guard_modify_chain_compose` — compose chainN' + chainM

### Throw + catch patterns
- `L1_hoare_modify_throw` — modify f; throw → (error, f s)
- `L1_hoare_modify_throw_catch` — modify f; throw with catch-compatible postcondition
- `L1_modify_throw_result` — result-level: {(error, f s)}
- `L1_catch_error_singleton` — catch on error singleton

### Result-level (non-Hoare)
- `L1_guard_modify_result` — {(ok, f s)} when guard holds
- `L1_guard_guard_modify_result` — double guard
- `L1_guard_guard_guard_modify_result` — triple guard
- `L1_seq_singleton_ok` — chain singleton results
- `L1_elim_cond_true` / `L1_elim_cond_false` — rewrite conditions away

### Heap reasoning
- `hVal_heapUpdate_same` — read back what you wrote
- `hVal_heapUpdate_disjoint` — other pointers unchanged (needs ptrDisjoint)
- `heapUpdate_preserves_heapPtrValid` — validity preserved through updates
- `heapPtrValid_different_type_disjoint` — different CType tags → disjoint

---

## 7. Spec Strengthening Checklist

Before proving a validHoare, check the spec's precondition includes:

- [ ] `heapPtrValid` for every pointer the function reads/writes
- [ ] `LinkedListValid` for any linked-list traversal
- [ ] `ptrDisjoint` for pointers that must not alias (e.g., node vs rb_state)
- [ ] Array element validity for array access (e.g., `∀ i < cap, heapPtrValid keys[i]`)
- [ ] For inter-procedural: callee's precondition must be derivable from caller's

If the precondition is too weak, the proof is IMPOSSIBLE (guards will fail, making ¬failed unprovable).
Strengthen the spec in `RBExtSpecs.lean` BEFORE attempting the proof.

---

## 8. Workflow for Eliminating a Sorry

1. **Read the spec** — Is the postcondition tautological? If so, note it (TASK-0231) but proceed.
2. **Read the L1 body** — What shape? (Pattern A-E above)
3. **Check the precondition** — Strong enough? (Section 7 checklist)
4. **Create proof file** — One sorry per file for heavy proofs (Section 4)
5. **Delegate to sub-agent** — See Section 9 below
6. **Verify the result** — See Section 10 below
7. **Commit** — One proof per commit for clean git history

---

## 9. Delegation Strategy (Sub-Agents)

**Always delegate sorry elimination to sub-agents.** Never write proofs inline in the main
conversation — it bloats the context window and wastes tokens on build output.

### Primary: swe-gardener with Opus

Launch a `swe-gardener` sub-agent with `model: "opus"` for each sorry:

```
Agent(
  subagent_type: "swe-gardener",
  model: "opus",
  run_in_background: true,
  prompt: "Prove <theorem> in <file>. Read <template> as reference. ..."
)
```

**Include in the prompt:**
- The exact file and line number
- Which proof pattern (A-E) applies
- A template proof to follow (e.g., "read rb_count_above_validHoare as template")
- The Locals field order (or where to find it)
- All rules: no validHoare_weaken_trivial_post, no fused bodies, anonymous constructors
- Build command: `pkill -f lean; sleep 2; lake build Examples.<File>`
- RAM warning: ONE build at a time, check `free -h` first

**Why Opus:** These proofs require sustained multi-step reasoning (reading L1 bodies,
defining step functions for 40 fields, writing projection lemmas, debugging build errors).
Opus handles this better than faster models. Expect 15-60 min per proof.

**Why background:** Builds take 5-15 min. Running in background lets you work on other
tasks or launch agents on non-overlapping files.

**One agent per file:** Never launch two agents on the same file — they'll conflict.
Multiple agents on DIFFERENT files is fine (but watch RAM — each build needs 5-10GB).

### Fallback: /model-race (sequential)

If Opus fails on a sorry after 2 attempts, try `/model-race`:

```
/model-race
TASK: Prove <theorem> in <file>
TARGET_FILES: <file>
VERIFY_CMD: lake build Examples.<Module> 2>&1 | tail -1 | grep -q "successfully"
```

**Sequential mode only** (one model at a time, 15 min timeout). Each model's `lake build`
needs 5-15GB RAM — parallel launches cause OOM.

Model-race works for:
- Pattern A (simple accessors) — ~80% success rate
- Pattern B (conditionals) — ~60% success rate
- Pattern D (loops WITH a template in the same file) — ~40% success rate

Model-race fails for:
- Pattern C (8+ step chains) — models use `{ s with ... }` → kernel depth
- Pattern D (loops WITHOUT template) — models can't invent step functions
- Pattern E (inter-procedural) — no infrastructure exists

### When to stop

If both Opus agent AND model-race fail on a sorry:
1. Check if the sorry is blocked on infrastructure (Section 2, Pattern E)
2. Check if the spec needs strengthening (Section 7)
3. Create a backlog task documenting what was tried and what's blocking
4. Move on to the next sorry

---

## 10. Verification Checklist (After Sub-Agent Completes)

Before committing a sub-agent's proof:

- [ ] **Sorry count decreased**: `grep -c '  sorry\|by sorry' <file>` — must be lower
- [ ] **Build passes**: `lake build Examples.<Module>` succeeds
- [ ] **No validHoare_weaken_trivial_post**: `grep validHoare_weaken_trivial_post <file>`
- [ ] **Correct satisfiedBy target**: `grep satisfiedBy <file>` shows `Module.l1_<func>_body`
- [ ] **No fused bodies**: `grep fused <file>` — should be empty
- [ ] **Anonymous constructors used**: `grep "{ s with locals" <file>` — should be empty in step functions
- [ ] **RAM check**: `free -h` — kill stale lean processes if <4GB free
