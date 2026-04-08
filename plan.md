# AutoCorres4: Lifting C into Lean 4 for Formal Verification

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
    |  Locals become function params/returns, not state fields
    v
[Stage 3: TypeStrengthen]   Lean 4 metaprogram + corres proof
    |  Tightest monad per function (pure/option/state/full)
    v
[Stage 4: HeapLift]         Lean 4 metaprogram + corres proof
    |  Flat bytes -> typed split heaps (Burstall-Bornat)
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

## Key Design Decisions

### C Front-End: Clang JSON (not a custom parser)

`clang -Xclang -ast-dump=json` produces a structured AST with type annotations. A Python script reads this and emits `.lean` files containing `CSimpl` terms.

Why clang over CompCert Clight parser: more practical (no OCaml dependency), handles full C preprocessing, stable JSON output.

The importer is trusted (it's in the TCB) but NOT proof-critical — the Lean kernel checks the CSimpl terms it produces. If the importer mistranslates, proofs about the wrong program succeed, but do not apply to the real C. This is the same trust model as seL4's StrictC parser.

Supported C subset (StrictC restrictions):
- No floating point (phase 1)
- No goto, longjmp, switch fall-through
- No address-of local variables
- No side effects in expressions
- No variadic functions, VLAs
- No pre/post increment in expressions

### CSimpl: The Deeply Embedded Imperative Language

```lean
inductive CSimpl (σ : Type) : Type where
  | skip    : CSimpl σ
  | basic   : (σ → σ) → CSimpl σ
  | seq     : CSimpl σ → CSimpl σ → CSimpl σ
  | cond    : (σ → Bool) → CSimpl σ → CSimpl σ → CSimpl σ
  | while   : (σ → Bool) → CSimpl σ → CSimpl σ
  | call    : FunName → CSimpl σ
  | guard   : (σ → Prop) → CSimpl σ → CSimpl σ   -- UB guard
  | throw   : CSimpl σ
  | catch   : CSimpl σ → CSimpl σ → CSimpl σ
  | spec    : (σ → σ → Prop) → CSimpl σ           -- nondeterministic spec
```

Simpler than Isabelle's Simpl (no concurrency). State type `σ` is a record with globals, locals, and flat byte memory.

Big-step semantics as an inductive relation `CSimpl.eval : CSimpl σ → σ → σ → Prop`.

### Monadic Framework

```lean
inductive CResult (α : Type) where
  | ok   : α → CResult α
  | fail : CError → CResult α    -- UB, overflow, null deref, etc.

def CStateM (σ α : Type) := σ → CResult (α × σ)

-- Hoare triples
def validHoare (P : σ → Prop) (m : CStateM σ α) (Q : α → σ → Prop) : Prop :=
  ∀ s₀, P s₀ → match m s₀ with
    | .ok (a, s₁) => Q a s₁
    | .fail _ => True

def totalHoare (P : σ → Prop) (m : CStateM σ α) (Q : α → σ → Prop) : Prop :=
  ∀ s₀, P s₀ → match m s₀ with
    | .ok (a, s₁) => Q a s₁
    | .fail _ => False

-- Refinement (correspondence) between stages
def corres (abs : σ' → σ) (concrete : CStateM σ α) (abstract : CStateM σ' α) : Prop :=
  ∀ s', match abstract s' with
    | .ok (a', t') => concrete (abs s') = .ok (a', abs t')
    | .fail e => concrete (abs s') = .fail e
```

After TypeStrengthen, functions get the tightest type:
- `pure : α` — no state, no failure
- `option : Option α` — may fail, no state
- `reader : σ → α` — reads state, no mutation, no failure
- `state : σ → α × σ` — stateful, no failure
- `full : CStateM σ α` — stateful + may fail

### Memory Model

Phase 1 (MVP): Flat byte array.
```lean
structure RawMem where
  bytes : Array UInt8

structure RawState where
  mem : RawMem
  globals : GlobalsRec  -- generated per-program record
  locals : LocalsRec    -- generated per-function record
```

Phase 3 (HeapLift): Split typed heaps.
```lean
structure LiftedState where
  heap_u32 : Fin maxAddr → UInt32
  valid_u32 : Fin maxAddr → Bool
  -- one pair per type used in the program
  globals : GlobalsRec
```

### Undefined Behavior

Modeled as `guard` nodes in CSimpl. The guard condition must be provable for the program to be correct. If UB occurs, the result is `CResult.fail .undefinedBehavior`. Total correctness proofs (totalHoare) prove absence of UB.

This is sound: any property proved under "UB causes failure" holds for any particular compiler's treatment of that UB.

## Dependency Graph

```
Mathlib (BitVec, omega, Int, Nat)
         |
    MonadLib                    CSemantics
    (CResult, CStateM,         (CSimpl, RawState,
     Hoare triples, corres)     eval, memory model)
         |                          |
         +----------+---------------+
                    |
              CImporter (Python: clang JSON -> .lean CSimpl defs)
                    |
         +----+----+----+----+
         |    |    |    |    |
       L1   L2   L3   L4   L5
    Simpl  Local Type Heap  Word
    Conv   Var   Str  Lift  Abs
         |    |    |    |    |
         +----+----+----+----+
                    |
              UserProofLib
           (c_vcg, c_step tactics)
```

## Phased Build Plan

### Phase 0: Foundation (Weeks 1-4)

**Goal**: MonadLib + CSemantics compile, hand-written test case works.

Build:
- `MonadLib.lean`: CResult, CStateM, Hoare triple defs, basic Hoare rules (seq, cond, while-invariant, frame), corres definition + transitivity
- `CSemantics.lean`: CSimpl inductive, CSimpl.eval big-step relation, RawState with flat byte memory
- Hand-write CSimpl for: `uint32_t max(uint32_t a, uint32_t b) { return a > b ? a : b; }`
- Prove a Hoare triple about it directly

**No C importer yet.** Test by manually encoding CSimpl terms.

**Exit criterion**: `theorem max_correct : totalHoare (fun s => True) max_simpl (fun r s => r = if a > b then a else b)` — proven and kernel-checked.

### Phase 1: Vertical Slice (Weeks 5-12)

**Goal**: Real `.c` file goes through entire pipeline (Stages 0-2), user proves property.

Build:
- `CImporter/import.py`: Parse clang JSON, emit .lean with CSimpl defs. Handle: integer types, local vars, if/else, while, return, arithmetic, comparisons.
- `Lifting/SimplConv.lean`: MetaM program converting CSimpl -> L1 monadic form + corres proof
- `Lifting/LocalVarExtract.lean`: MetaM program lifting locals out of state + corres proof
- Skip TypeStrengthen, HeapLift, WordAbstract — users work at L2 with BitVec + raw state

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

**Exit criterion**: User writes `theorem gcd_divides : totalHoare P l2_gcd Q` in Lean 4, proves it, proof chains back to the actual C via composed corres lemmas.

### Phase 2: Clean Types (Weeks 13-20)

**Goal**: TypeStrengthen + WordAbstract produce functions with clean Lean types.

Build:
- `Lifting/TypeStrengthen.lean`: Analyze failure paths, emit tightest monad + corres proof
- `Lifting/WordAbstract.lean`: BitVec -> Int/Nat with range guards + corres proof. Heavy use of Mathlib BitVec lemmas + omega.
- `Tactics/CStep.lean`: c_step tactic (like Aeneas's progress) — unfold one monadic step, apply function spec

**Exit criterion**: gcd lifts to `Nat -> Nat -> Nat`. User proofs use omega and Nat reasoning, not BitVec.

### Phase 3: Pointers + Structs (Weeks 21-30)

**Goal**: Programs with pointers and structs get typed heap access.

Build:
- Struct support in CImporter (field access, struct pointers)
- Array indexing with bounds proofs
- `Lifting/HeapLift.lean`: Split raw memory into per-type typed heaps + corres proof
- Pointer validity predicates

Target C:
```c
struct node { int val; struct node *next; };
int list_length(struct node *head) {
    int count = 0;
    while (head != NULL) { count++; head = head->next; }
    return count;
}
```

**Exit criterion**: User verifies list_length returns length of abstract `List Nat`, reasoning about lists not bytes.

### Phase 4: Scale + Automation (Weeks 31-40)

Build:
- `Tactics/CVcg.lean`: Full VCG that applies Hoare rules automatically, leaving only "interesting" obligations
- AI proof search integration: `ai_prove` tactic that serializes goal, calls LLM, applies result
- `sorry`-extraction tool: scan .lean files, package obligations as structured ProofTasks
- Function pointers / dispatch tables
- Test on real embedded C (~500-1000 LOC)

### Phase 5: Separation Logic (Weeks 41+)

- Separation logic predicates over split heap
- Frame rule, magic wand
- `sep_auto` tactic
- Scale to thousands of LOC

## AI Integration Points

**Principle**: AI never extends the trusted base. Every AI output is kernel-checked. Deterministic tactics first (grind, omega, decide, simp), AI fills gaps.

### Where AI helps most (by impact):

1. **Loop invariant generation** (highest value) — Given loop body + pre/postcondition, AI proposes invariant. Lean checks.
2. **Correspondence proofs between stages** — Formulaic but tedious. AI drafts tactic scripts following patterns.
3. **Data structure invariant generation** — Given struct + operations, AI proposes well-formedness predicate.
4. **Specification drafting** — Given C function + types, AI drafts theorem statement. Human approves.
5. **Overflow guard discharge** — AI + omega close arithmetic obligations.

### Tactic priority stack (for any obligation):

1. `decide` (decidable finite props)
2. `omega` (linear integer arithmetic)
3. `simp [lemma_set]` (rewriting)
4. `grind` (congruence closure + E-matching + arithmetic, 5s timeout)
5. `corres_auto` (custom: unfold + simulation lemmas)
6. `Aesop` (goal-directed search)
7. `ai_prove` (LLM oracle, N retries)
8. `sorry` with structured error report for human

### Reward signal for AI training:

- Kernel accepts proof -> reward 1.0
- Tactic reduces goal count -> reward 0.3-0.7
- Tactic type-errors -> reward -0.1
- Build a RAG index over proven lemmas, retrieve similar proofs in-context

## Risks

1. **Proof term size**: AutoCorres in Isabelle generates large terms. Lean 4 kernel may be slower. Mitigation: measure in Phase 0, use native_decide where possible.
2. **C semantics fidelity**: Getting integer promotion, implicit conversions, struct layout right is tedious and error-prone. Mitigation: start with uint32_t only, expand incrementally. Follow CompCert's well-studied semantics.
3. **grind coverage unknown**: We don't know what % of obligations grind handles. Mitigation: benchmark in Phase 1 with representative goals.
4. **Metaprogramming complexity**: Each lifting stage is hundreds of lines of MetaM. Lean 4 metaprogramming docs are sparse. Mitigation: study Aeneas's tactic code as template.
5. **Clang JSON stability**: Not formally versioned. Mitigation: pin LLVM version, regression tests.

## What We Reuse

- **Aeneas patterns**: CResult type, progress/step tactic pattern, scalar modeling
- **Mathlib**: BitVec lemmas, omega, algebraic structures
- **grind**: Primary workhorse for "boring" proof obligations
- **lean-mlir/SSA**: Denotational semantics style, peephole rewrite patterns
- **CompCert Clight semantics**: As reference (not ported, but followed) for what each C construct means

## Verification of the Plan Itself

After Phase 1, we have a concrete test: take `gcd.c`, run the pipeline, prove gcd_divides in Lean 4, and verify the proof chains all the way back to the C semantics. If this works end-to-end, the architecture is validated. If it doesn't, we learn what breaks before investing in Phases 2-5.
