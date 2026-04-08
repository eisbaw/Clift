# Clift: Lifting C into Lean 4 for Formal Verification

## Context

We want to verify imperative C code with the same rigor as seL4, but using Lean 4 instead of Isabelle/HOL. The "semantic replacement" approach (lean-zip) is insufficient — it proves a *rewrite* correct, not the *original* C. We need to verify the C that actually runs.

seL4's AutoCorres pipeline (Isabelle/HOL) is the gold standard: parse C, embed it formally, lift through abstraction stages, prove properties that chain back to the actual C. We replicate this in Lean 4 to access its AI ecosystem (grind, LLM proof search, Mathlib).

## Architecture: The Pipeline

```
C source (.c)
    |  clang -ast-dump=json
    v
[Stage 0: CImporter]       Python script, reads JSON, emits .lean files
    |  CSimpl terms (deeply embedded imperative language)
    v
[Stage 1: SimplConv]        Lean 4 metaprogram + corres proof
    |  Shallow monadic embedding (raw state monad + failure)
    v
[Stage 2: LocalVarExtract]  Lean 4 metaprogram + corres proof
    |  Locals become lambda-bound Lean variables, not state fields
    v
[Stage 3: TypeStrengthen]   Lean 4 metaprogram + corres proof
    |  Tightest monad per function (pure/gets/option/nondet)
    v
[Stage 4: HeapLift]         Lean 4 metaprogram + corres proof
    |  Flat bytes -> typed split heaps (simplified Burstall-Bornat)
    v
[Stage 5: WordAbstract]     Lean 4 metaprogram + corres proof
    |  BitVec n -> Int/Nat with range guards
    v
[User writes specs + proofs about clean functional model]
    |  Correctness chains back to C via composed corres lemmas
    v
Verified C
```

Each stage produces:
1. A transformed function definition
2. A machine-checked `corres` lemma proving the transformation preserves all behaviors

The stages are **sequential** — each stage's input is the previous stage's output. They cannot be developed in parallel (though their foundations can be).

## Key Design Decisions

### Decision 1: Refinement Direction — Backward Simulation

Following seL4's `corres_underlying`, we use **backward simulation**: "for every concrete result, there exists a matching abstract result."

```lean
-- Backward simulation: concrete behaviors are contained in abstract behaviors.
-- srel: state relation (pairs of abstract × concrete states)
-- nf/nf': no-fail flags (when true, that side must not fail)
-- rrel: return value relation
-- G/G': preconditions on abstract/concrete state
def corres
    (srel : σ → σ' → Prop)      -- state relation
    (nf : Bool) (nf' : Bool)     -- no-fail flags
    (rrel : α → β → Prop)       -- return value relation
    (G : σ → Prop) (G' : σ' → Prop)  -- guards (preconditions)
    (m : CStateM σ α)           -- abstract
    (m' : CStateM σ' β)         -- concrete
    : Prop :=
  ∀ s s', srel s s' → G s → G' s' →
    -- if nf, abstract must not fail
    (nf → m s ≠ .fail) →
    -- for every concrete result, abstract has a matching one
    (∀ r' t', m' s' = .ok (r', t') →
      ∃ r t, m s = .ok (r, t) ∧ srel t t' ∧ rrel r r') ∧
    -- if nf', concrete must not fail
    (nf' → m' s' ≠ .fail)
```

**Why backward, not forward**: backward simulation says "the concrete cannot do anything the abstract cannot." This is what we want — the abstract spec is an *overapproximation* of the concrete. Properties proved about the abstract hold for the concrete. Forward simulation would require the abstract to match every concrete step, which is too strong when the abstract is nondeterministic.

### Decision 2: C Front-End — Clang JSON

`clang -Xclang -ast-dump=json` produces a structured AST with type annotations. A Python script reads this and emits `.lean` files containing `CSimpl` terms.

Why clang over CompCert Clight parser: more practical (no OCaml dependency), handles full C preprocessing.

**Trust model**: The importer IS in the TCB. If it mistranslates C to CSimpl, proofs are about the wrong program and do not apply to the real C. This is the same trust model as seL4's StrictC parser. Mitigation: extensive regression tests against known C semantics edge cases, and differential testing against CompCert's parser for the shared subset.

**Clang JSON stability risk**: Not formally versioned. Mitigation: pin to a specific LLVM version via nix flake, regression tests on every update.

Supported C subset (StrictC restrictions):
- No floating point (phase 1)
- No goto, longjmp, switch fall-through
- No address-of local variables
- No side effects in expressions
- No variadic functions, VLAs
- No pre/post increment in expressions

### Decision 3: One Global State Record (Following seL4)

Following seL4's C parser exactly: **one state record for ALL functions**, not per-function records. Local variables from all functions are merged into a single `LocalsRec`. Same-name, same-type locals share a field. Same-name, different-type locals get type-qualified names.

```lean
-- Base state: globals + raw heap
structure Globals where
  rawHeap : HeapRawState     -- byte-level memory + type descriptor
  -- plus one field per non-addressed global variable

-- Locals: ONE record for ALL functions in the .c file
-- Generated per-program by the importer
structure Locals where
  a_unsigned : UInt32         -- local 'a' from gcd()
  b_unsigned : UInt32         -- local 'b' from gcd()
  t_unsigned : UInt32         -- local 't' from gcd()
  -- ... all locals from all functions ...

-- The full state — parametric, same type for all CSimpl commands
structure CState where
  globals : Globals
  locals : Locals
```

Function calls use save/restore of caller's locals (via `DynCom`-style state capture), matching Simpl's approach. The `call` constructor captures the current state, sets up parameters, and restores on return.

LocalVarExtract (L2) then eliminates the locals from the state, lifting them into Lean-level lambda-bound variables. After L2, the ugly global locals record is gone and functions look natural.

### Decision 4: CSimpl — The Deeply Embedded Imperative Language

```lean
-- Deeply embedded imperative language, parametric in state type σ
-- and procedure environment Γ (maps procedure names to bodies)
inductive CSimpl (σ : Type) where
  | skip    : CSimpl σ
  | basic   : (σ → σ) → CSimpl σ
  | seq     : CSimpl σ → CSimpl σ → CSimpl σ
  | cond    : (σ → Bool) → CSimpl σ → CSimpl σ → CSimpl σ
  | while   : (σ → Bool) → CSimpl σ → CSimpl σ
  | call    : ProcName → CSimpl σ
  | guard   : (σ → Prop) → CSimpl σ → CSimpl σ   -- UB guard
  | throw   : CSimpl σ
  | catch   : CSimpl σ → CSimpl σ → CSimpl σ
  | spec    : (σ → σ → Prop) → CSimpl σ           -- nondeterministic spec
  | dynCom  : (σ → CSimpl σ) → CSimpl σ           -- state-dependent command (for call setup)
```

### Decision 5: Big-Step Inductive Semantics (Following Simpl)

Following Simpl exactly: big-step semantics as an **inductive relation** (least fixed point). Non-terminating loops simply have no derivation — this naturally gives **partial correctness**.

```lean
-- Execution outcomes
inductive Outcome (σ : Type) where
  | normal : σ → Outcome σ
  | abrupt : σ → Outcome σ    -- break/continue/return
  | fault  : Outcome σ         -- UB triggered

-- Big-step inductive semantics
inductive Exec (Γ : ProcEnv σ) : CSimpl σ → σ → Outcome σ → Prop where
  | skip      : Exec Γ .skip s (.normal s)
  | basic     : Exec Γ (.basic f) s (.normal (f s))
  | seqNormal : Exec Γ c₁ s (.normal t) → Exec Γ c₂ t u → Exec Γ (.seq c₁ c₂) s u
  | seqAbrupt : Exec Γ c₁ s (.abrupt t) → Exec Γ (.seq c₁ c₂) s (.abrupt t)
  | condTrue  : b s = true  → Exec Γ c₁ s t → Exec Γ (.cond b c₁ c₂) s t
  | condFalse : b s = false → Exec Γ c₂ s t → Exec Γ (.cond b c₁ c₂) s t
  | whileTrue : b s = true  → Exec Γ c s (.normal t) → Exec Γ (.while b c) t u →
                Exec Γ (.while b c) s u
  | whileFalse: b s = false → Exec Γ (.while b c) s (.normal s)
  | guardOk   : p s → Exec Γ c s t → Exec Γ (.guard p c) s t
  | guardFault: ¬ p s → Exec Γ (.guard p c) s .fault
  -- ... throw, catch, call, dynCom rules
```

**Termination** is a separate inductive predicate (following Simpl's `terminates`), not fuel-based. Total correctness = partial correctness + termination.

This is NOT computable — you cannot `#eval` an Exec derivation. Testing uses the CImporter's test suite against the C compiler, not Lean evaluation.

### Decision 6: Monadic Framework

```lean
-- The nondeterministic state monad with failure (seL4's nondet_monad)
-- Results are a set of (return, state) pairs + a failure flag
structure NondetM (σ α : Type) where
  run : σ → { results : Set (α × σ) // failed : Bool }

-- Hoare triples (partial and total correctness)
def validHoare (P : σ → Prop) (m : NondetM σ α) (Q : α → σ → Prop) : Prop :=
  ∀ s₀, P s₀ → ¬(m.run s₀).failed ∧
    ∀ (r, s₁) ∈ (m.run s₀).results, Q r s₁

def totalHoare (P : σ → Prop) (m : NondetM σ α) (Q : α → σ → Prop) : Prop :=
  validHoare P m Q  -- partial correctness
  ∧ ∀ s₀, P s₀ → (m.run s₀).results.Nonempty  -- must terminate (produce ≥1 result)
```

### Decision 7: TypeStrengthen — 3 Monad Levels (not 5)

Following seL4's AutoCorres which uses 4 (pure/gets/option/nondet), we start with **3** for the MVP:

1. **`pure`** (precedence 100) — No state, no failure. Target: `α`
2. **`option`** (precedence 60) — May fail, reads/writes state. Target: `σ → Option (α × σ)`
3. **`nondet`** (precedence 0, default) — Full nondeterministic monad. Target: `NondetM σ α`

Add `gets` (read-only state) later when the infrastructure is mature.

### Decision 8: Memory Model

**Phase 1 (MVP)**: Flat byte array + type descriptor.
```lean
-- Byte-level heap with type tracking (following seL4's UMM)
structure HeapRawState where
  mem : Fin memSize → UInt8           -- byte-addressed memory
  htd : Fin memSize → Option TypeTag  -- what type is stored here

-- Pointer with type tag
structure Ptr (α : Type) where
  addr : Fin memSize
```

**Phase 3 (HeapLift)**: Simplified split heap (following AutoCorres's `TypHeapSimple`, NOT the full Tuch model). Each typed pointer maps to `Option α`:

```lean
-- After HeapLift: simple_lift style (one type per address, no nested field pointers)
def simpleLift (s : HeapRawState) (p : Ptr α) : Option α :=
  if heapPtrValid s.htd p then some (hVal s.mem p) else none
```

**Restriction** (same as AutoCorres): nested struct field access via sub-pointers is NOT supported in the lifted heap. You access structs as whole values, not by taking pointers to individual fields.

**Struct layout, padding, alignment**: Modeled via typeclass instances (`CType`, `MemType`) that encode size, alignment, and field offsets for each struct. Generated by the importer based on the target platform's ABI.

### Decision 9: Separation Logic Predicates in Phase 3 (not Phase 5)

Basic separation logic predicates (`mapsTo`, `sep`, frame rule) are needed to reason about pointers. Define them alongside HeapLift in Phase 3, not deferred to Phase 5. Phase 5 adds *automation* (`sep_auto` tactic), not the predicates themselves.

## Dependency Graph

```
Mathlib (BitVec, omega, Int, Nat)
         |
    MonadLib                    CSemantics
    (NondetM, Hoare triples,    (CSimpl, Exec, CState,
     corres, monad laws)         HeapRawState)
         |                          |
         +----------+---------------+
                    |
              CImporter (Python: clang JSON -> .lean CSimpl defs)
                    |
                    v
              L1: SimplConv  (CSimpl -> NondetM, + corres proof)
                    |
                    v
              L2: LocalVarExtract  (lift locals to lambda-bound vars, + corres proof)
                    |
                    v
              L3: TypeStrengthen  (narrow monad: pure/option/nondet, + corres proof)
                    |
                    v
              L4: HeapLift  (raw bytes -> typed heaps + sep logic preds, + corres proof)
                    |
                    v
              L5: WordAbstract  (BitVec -> Int/Nat + range guards, + corres proof)
                    |
                    v
              UserProofLib (c_vcg, c_step, sep_auto tactics)
```

## Phased Build Plan

### Phase 0: Foundation (Weeks 1-4)

**Goal**: MonadLib + CSemantics compile, hand-written test cases work, MetaM feasibility validated.

Build:
- `MonadLib`: NondetM, Hoare triple defs, basic Hoare rules (seq, cond, while-invariant, frame), `corres` definition (backward simulation) + transitivity
- `CSemantics`: CSimpl inductive, Exec big-step inductive relation, HeapRawState, CState with globals + locals
- Hand-write CSimpl for: `uint32_t max(uint32_t a, uint32_t b) { return a > b ? a : b; }`
- Prove a Hoare triple about it directly
- **MetaM feasibility test**: Write a trivial Lean 4 metaprogram that constructs a CSimpl term and proves something about it programmatically

**Exit criteria**:
1. `theorem max_correct : validHoare (...) max_simpl (...)` — proven and kernel-checked
2. MetaM test: metaprogram constructs a term and discharges a proof obligation
3. Measure: proof term size for max_correct, kernel check time. Extrapolate to 100-line functions.

### Phase 1: Vertical Slice (Weeks 5-14)

**Goal**: Real `.c` file goes through pipeline (Stages 0-2), user proves property.

Build:
- `CImporter/import.py`: Parse clang JSON, emit .lean with CSimpl defs + state records. Handle: integer types, local vars, if/else, while, return, arithmetic, comparisons.
- `Lifting/SimplConv.lean`: MetaM converting CSimpl -> L1 NondetM + corres proof
- `Lifting/LocalVarExtract.lean`: MetaM lifting locals to lambda-bound vars + corres proof

**CImporter interface contract** (the key boundary):
- Input: clang JSON AST for one .c file
- Output: one `.lean` file containing:
  - `structure Globals` (per-program)
  - `structure Locals` (all locals from all functions, merged)
  - `structure CState` (globals + locals)
  - `def <func>_body : CSimpl CState` for each function
  - `def procEnv : ProcEnv CState` (maps names to bodies)

**Do NOT start CImporter until CSimpl and CState design is frozen** (end of Phase 0).

Target C:
```c
uint32_t gcd(uint32_t a, uint32_t b) {
    while (b != 0) {
        uint32_t t = b;
        b = a % b;
        a = t;
    }
    return a;
}
```

**Exit criteria**:
1. CImporter: parse gcd.c, emit .lean, the .lean compiles
2. SimplConv: L1 monadic form generated with corres proof
3. LocalVarExtract: L2 form with locals as lambda params
4. User proves `theorem gcd_correct : validHoare P l2_gcd Q`, proof chains to C

### Phase 2: Clean Types (Weeks 15-24)

**Goal**: TypeStrengthen + WordAbstract produce clean Lean types.

Build:
- `Lifting/TypeStrengthen.lean`: Analyze L2 functions for failure paths, emit tightest monad (pure/option/nondet) + corres proof
- `Lifting/WordAbstract.lean`: BitVec -> Int/Nat with range guards + corres proof. Heavy use of Mathlib BitVec lemmas + omega.
- `Tactics/CStep.lean`: c_step tactic — unfold one monadic step, apply function spec

**Exit criterion**: gcd lifts to `Nat → Nat → Nat` (pure). User proofs use omega and Nat reasoning, not BitVec.

### Phase 3: Pointers + Structs + Sep Logic Basics (Weeks 25-44)

**Goal**: Programs with pointers and structs get typed heap access with frame reasoning.

**This is the hardest phase. Budget 20 weeks, not 10.**

Build (sub-phased):
- **3a (weeks 25-30)**: Single-level pointers to scalars. `Ptr UInt32` read/write with validity proofs. No structs yet.
- **3b (weeks 31-36)**: Struct support in CImporter (field access, struct pointers). `CType`/`MemType` typeclasses for layout. Struct padding/alignment modeled.
- **3c (weeks 37-40)**: HeapLift — `simpleLift` from raw bytes to typed heaps + corres proof.
- **3d (weeks 41-44)**: Basic separation logic predicates (`mapsTo`, `sep`, frame rule). No automation yet — manual proofs.

Target C (3a — scalar pointers):
```c
void swap(uint32_t *a, uint32_t *b) {
    uint32_t t = *a;
    *a = *b;
    *b = t;
}
```

Target C (3c — structs + linked data):
```c
struct node { int val; struct node *next; };
int list_length(struct node *head) {
    int count = 0;
    while (head != NULL) { count++; head = head->next; }
    return count;
}
```

**Exit criteria**:
1. swap: prove `*a` and `*b` are exchanged, frame: other memory unchanged
2. list_length: verify returns length of abstract `List Nat`

### Phase 4: Automation (Weeks 45-54)

Build:
- `Tactics/CVcg.lean`: Full VCG applying Hoare rules automatically
- `Tactics/SepAuto.lean`: Separation logic automation (frame rule, points-to rewriting)
- `corres_auto` tactic for correspondence proofs
- AI proof search integration (details TBD after Phase 2 experience)
- Test on real embedded C (~500-1000 LOC)

### Phase 5: Scale (Weeks 55+)

- Function pointers / dispatch tables
- Concurrency (interrupt handlers)
- Scale to thousands of LOC
- Performance optimization (incremental re-verification)

## Risks

1. **Proof term size**: AutoCorres in Isabelle generates large terms. Lean 4 kernel may be slower. Mitigation: measure in Phase 0, use native_decide where possible. Hard exit: if max_correct takes >5s to check, redesign proof strategy.
2. **C semantics fidelity**: Integer promotion, implicit conversions, struct layout. Mitigation: start with uint32_t only, expand incrementally. Follow CompCert Clight as reference.
3. **grind coverage unknown**: Mitigation: benchmark in Phase 0 with representative goals.
4. **MetaM complexity**: Lean 4 metaprogramming docs sparse. Mitigation: Phase 0 feasibility test. Study Aeneas tactic code as template.
5. **Clang JSON stability**: Mitigation: pin LLVM via nix flake, regression tests.
6. **Lean 4 / Mathlib version churn**: 40+ week project will see upstream breakage. Mitigation: pin `lean-toolchain` + exact Mathlib commit in `lakefile.lean`. Update deliberately, not reactively.
7. **Phase 3 memory model correctness**: Silent semantic mismatch between our heap model and what gcc actually does for struct layout/padding would invalidate all pointer proofs. Mitigation: differential testing of struct sizes/offsets against gcc output.
8. **Clang AST trust gap**: If clang's JSON AST misrepresents C semantics (e.g., wrong integer promotion in AST), the entire pipeline is silently wrong. Mitigation: test edge cases (integer promotion, sign extension, implicit conversions) against known C standards behavior.

## What We Reuse

- **Aeneas patterns**: Result type, progress/step tactic, scalar modeling
- **Mathlib**: BitVec lemmas, omega, algebraic structures
- **grind**: Primary workhorse for "boring" proof obligations
- **lean-mlir/SSA**: Denotational semantics style, peephole rewrite patterns
- **CompCert Clight semantics**: As reference for what each C construct means
- **seL4 l4v source**: Direct reference for corres, Exec, TypeStrengthen design

## AI Integration

**Principle**: AI never extends the trusted base. Every AI output is kernel-checked. Deterministic tactics first (grind, omega, decide, simp), AI fills gaps. Details deferred to Phase 4 — get the deterministic pipeline working first.

## Verification of the Plan Itself

After Phase 1, we have a concrete test: take `gcd.c`, run the pipeline, prove gcd_correct in Lean 4, verify the proof chains back to C semantics. If this works end-to-end, the architecture is validated. If it doesn't, we learn what breaks before investing in Phases 2-5.
