# Proof Style Guide: Conventions for Maintainable Clift Proofs

This document defines proof conventions for the Clift project. Without
consistent style, proof maintenance becomes impossible as the codebase
grows. seL4 learned this the hard way -- adopt conventions early.

## 1. Tactic Conventions

### When to Use Each Tactic

| Tactic | Use when | Avoid when |
|--------|----------|------------|
| `rfl` | Both sides are definitionally equal | Need unfolding first |
| `simp` | Goal follows from simp lemmas | Need precise control over rewrites |
| `omega` | Linear arithmetic over Nat/Int/UInt | Non-linear or modular arithmetic |
| `rw [...]` | Need specific rewrite at specific location | `simp` would close the goal |
| `exact` | You have the exact proof term | Building it would be clearer with tactics |
| `apply` | Reducing to subgoals via a lemma | `exact` would work directly |
| `unfold` | Need to expose a definition body | The definition is already unfolded |
| `intro` | Moving hypotheses from goal to context | Goal is not a forall/implication |
| `constructor` | Goal is a conjunction or exists | Not a product type |
| `cases` / `rcases` | Destructing a hypothesis | Pattern match would be clearer |

### Preferred Ordering

1. **Unfold definitions first**: `unfold func_name`
2. **Simplify structure**: `simp` or `simp only [...]`
3. **Case split if needed**: `cases`, `rcases`, `split`
4. **Arithmetic last**: `omega`, `norm_num`

### Automation Preferences

Prefer automation over manual steps, but use `simp only [...]` over bare `simp`
for proofs that must survive library changes.

```lean
-- GOOD: explicit simp set, survives Mathlib updates
theorem foo : ... := by
  simp only [swap_f1_globals, swap_f1_locals_a]

-- ACCEPTABLE: when the simp set is stable
theorem bar : ... := by
  simp [swap_f1, swap_f2]

-- BAD: depends on global simp set which changes
theorem baz : ... := by
  simp
```

## 2. Naming Conventions

### Theorems and Lemmas

Pattern: `<subject>_<property>_<qualifier>`

```
l1_gcd_body_corres        -- L1corres for gcd_body
swap_spec_sat             -- FuncSpec.satisfiedBy for swap
swap_f1_globals           -- projection: (swap_f1 s).globals
gcd_correct_nat           -- correctness at Nat level
rb_push_preserves_count   -- invariant preservation
```

### Naming Rules

- L1corres proofs: `l1_<func>_body_corres`
- Hoare triples: `<func>_spec_sat`
- Projection lemmas: `<step_func>_<field>`
- Correctness: `<func>_correct[_<type>]`
- Preservation: `<func>_preserves_<property>`
- Helper lemmas: `<func>_<description>_aux` or `<func>_<description>_helper`

### Step Functions

For the decomposed L1 proof pattern, name step functions sequentially:

```lean
def swap_f1 ...  -- step 1: t := *a
def swap_f2 ...  -- step 2: *a := *b
def swap_f3 ...  -- step 3: *b := t
```

## 3. The `[local irreducible]` Pattern

### Problem

Lean 4's kernel sometimes unfolds `hVal` and `heapUpdate` deeply,
causing exponential blowup in type-checking time. This manifests as
`maxRecDepth` or `maxHeartbeats` errors.

### Solution

Mark heap operations as locally irreducible. This prevents the kernel from
unfolding them, forcing proofs to go through simp lemmas instead.

```lean
-- GOOD: prevents kernel blowup on heap proofs
@[simp] theorem swap_f2_globals_rawHeap (s : ProgramState) :
    (swap_f2 s).globals.rawHeap =
      heapUpdate s.globals.rawHeap s.locals.a (hVal s.globals.rawHeap s.locals.b) := by
  local irreducible_def hVal heapUpdate
  unfold swap_f2; rfl
```

### When to Use

- Any simp lemma whose statement or proof involves `hVal` or `heapUpdate`
- Any theorem about heap state after a pointer write
- Projection lemmas for step functions that modify the heap

### When NOT to Use

- Pure local-variable proofs (no heap involved)
- Top-level Hoare triples (use at the lemma level, not the theorem level)
- L1corres proofs (these are structural, no heap reasoning)

## 4. Template: validHoare Proofs

### Structure

```lean
/-- Specification for function foo. -/
theorem foo_spec_sat :
    validHoare
      (fun s => P s)          -- precondition
      l1_foo_body              -- the L1 monadic body
      (fun s r => Q s r)       -- postcondition
:= by
  -- Step 1: unfold the L1 body into combinators
  unfold l1_foo_body foo_step1 foo_step2

  -- Step 2: apply Hoare rules for each combinator
  apply validHoare_seq
  · -- First sub-goal: step 1
    apply validHoare_guard_modify
    intro s hs
    simp only [foo_f1_field1, foo_f1_field2]
    exact ⟨guard_condition, post_condition⟩
  · -- Second sub-goal: step 2
    apply validHoare_modify
    intro s hs
    simp only [foo_f2_field1]
    exact post_condition
```

### Key Principles

1. **Decompose into steps**: Each `L1.modify` gets its own step function
   and projection lemmas.
2. **Work at the combinator level**: Use Hoare rules for seq/guard/modify,
   not raw NondetM unfolding.
3. **Projection lemmas do the work**: The simp set should close most
   field-equality subgoals automatically.
4. **State the intermediate invariant explicitly** when using `validHoare_seq`.

## 5. Template: L1corres Proofs

### Structure

```lean
/-- L1corres: the L1 monadic body corresponds to the CSimpl body. -/
theorem l1_foo_body_corres :
    L1corres Foo.procEnv l1_foo_body Foo.foo_body := by
  -- Step 1: unfold both sides
  unfold l1_foo_body Foo.foo_body

  -- Step 2: structural decomposition (mirrors CSimpl structure)
  apply L1corres_catch
  · apply L1corres_seq
    · apply L1corres_guard; exact L1corres_basic _ _
    · apply L1corres_seq
      · exact L1corres_basic _ _
      · apply L1corres_guard; exact L1corres_basic _ _
  · exact L1corres_skip _
```

### Key Principles

1. **Mirror the CSimpl structure**: The proof follows the shape of `foo_body`.
2. **One combinator rule per CSimpl constructor**:
   - `.catch` -> `L1corres_catch`
   - `.seq` -> `L1corres_seq`
   - `.guard` -> `L1corres_guard`
   - `.basic` -> `L1corres_basic`
   - `.while` -> `L1corres_while`
   - `.skip` -> `L1corres_skip`
   - `.throw` -> `L1corres_throw`
3. **These proofs should be automatable** (and are targets for `corres_auto`).

## 6. Good vs Bad Examples

### Good: Decomposed step functions with projections

```lean
-- Step function with explicit constructor (not { s with ... })
private noncomputable def swap_f1 (s : ProgramState) : ProgramState :=
  ⟨s.globals, ⟨s.locals.a, s.locals.b, hVal s.globals.rawHeap s.locals.a⟩⟩

-- Projection lemma with [local irreducible]
@[simp] theorem swap_f1_globals (s : ProgramState) :
    (swap_f1 s).globals = s.globals := by
  unfold swap_f1; rfl
```

### Bad: Inline complex expressions without projections

```lean
-- BAD: everything inline, no decomposition, kernel will choke
theorem swap_correct : validHoare (fun s => ...) (
    L1.seq (L1.guard (fun s => heapPtrValid s.globals.rawHeap s.locals.a)
      (L1.modify (fun s => ⟨s.globals, ⟨s.locals.a, s.locals.b,
        hVal s.globals.rawHeap s.locals.a⟩⟩)))
    (L1.seq ...)) (fun s r => ...) := by
  sorry -- will never close: terms too deeply nested for the kernel
```

### Good: Named intermediate states

```lean
-- GOOD: each step has a name and can be reasoned about independently
theorem swap_step1_valid : validHoare P swap_l1_step1 Q1 := by ...
theorem swap_step2_valid : validHoare Q1 swap_l1_step2 Q2 := by ...
theorem swap_step3_valid : validHoare Q2 swap_l1_step3 Q := by ...
```

### Bad: Monolithic proof with deep nesting

```lean
-- BAD: one giant proof term, impossible to debug or maintain
theorem swap_correct : ... := by
  unfold l1_swap_body; simp; intro s h; cases h; constructor
  <100 lines of tactics>
  omega
```

### Good: Explicit simp set

```lean
simp only [swap_f1_globals, swap_f1_locals_a, swap_f1_locals_b,
           hVal_heapUpdate_same, heapUpdate_preserves_heapPtrValid]
```

### Bad: Bare simp (fragile, slow)

```lean
simp  -- which lemmas? Will this survive the next Mathlib update?
```

## 7. When to Split into Helper Lemmas

Split a lemma when:

1. **The proof is longer than ~20 tactic lines** -- break into sub-lemmas
2. **The goal has a conjunction** -- prove each conjunct separately
3. **The same sub-proof appears twice** -- extract and reuse
4. **Heap reasoning is needed** -- projection lemmas are mandatory
5. **The `maxHeartbeats` limit is hit** -- decompose to reduce kernel work

Do NOT split when:

1. The proof is `rfl` or `omega` -- trivial proofs stay inline
2. Splitting would require restating complex hypotheses
3. The sub-lemma would only be used once and is under 5 lines

## 8. Proofs That Survive C Code Changes

When the C source changes, `CImporter` regenerates `Generated/*.lean`.
Proofs break if they depend on the exact structure of the generated code.

### Strategies for Resilience

1. **Prove against specs, not implementations**: Write FuncSpec and prove
   `satisfiedBy`, not raw CSimpl structure.
2. **Use L1corres as the abstraction boundary**: Changes in CSimpl structure
   only break L1corres proofs, not Hoare proofs above them.
3. **Projection lemmas as shock absorbers**: When the step function body
   changes, only the projection lemma proofs need updating (they're `rfl`).
4. **Avoid hard-coding line numbers or structure positions** in proofs.

## 9. maxHeartbeats and maxRecDepth

Set these at the file level, not per-theorem:

```lean
set_option maxHeartbeats 12800000  -- for files with heap proofs
set_option maxRecDepth 16384      -- for deeply nested structures
```

If a single theorem needs more heartbeats, that's a signal to decompose it
further, not to raise the limit.
