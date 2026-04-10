-- AI-assisted data structure invariant generation framework
--
-- Complements InvariantGen.lean (loop invariants) with struct invariants.
-- Given a C struct and its operations, an AI proposes a well-formedness
-- invariant. The invariant is kernel-checked via the GlobalInvariant
-- framework from Clift/Lifting/GlobalInvariant.lean.
--
-- Examples of struct invariants:
-- - Ring buffer: count <= capacity, null-consistency
-- - Linked list: next pointers form acyclic chain
-- - BST: ordering property on all nodes
-- - Red-black tree: color invariant + black-height balance
--
-- Reference: task-0100

import Clift.Lifting.GlobalInvariant
import Clift.Lifting.FuncSpec
import Clift.AI.InvariantGen

/-! # StructContext: what the AI needs to know about a data structure -/

/-- The context for a data structure that an AI needs to generate an invariant.
    This captures the struct type and the operations that manipulate it. -/
structure StructContext (σ : Type) where
  /-- Human-readable name of the struct (e.g., "rb_state", "node") -/
  structName : String
  /-- Human-readable field descriptions -/
  fieldDescriptions : List (String × String)  -- (fieldName, typeDescription)
  /-- Operations that manipulate this struct, with their L1 bodies -/
  operations : List (String × L1Monad σ)  -- (opName, body)
  /-- Any known constraints from the C code (e.g., from asserts, comments) -/
  knownConstraints : List String

/-- A suggested struct invariant with metadata. -/
structure StructInvariantSuggestion (σ : Type) where
  /-- The invariant predicate -/
  inv : GlobalInvariant σ
  /-- Human-readable description -/
  description : String
  /-- Which fields are constrained by this invariant -/
  constrainedFields : List String

/-! # Struct invariant oracle -/

/-- An oracle for struct invariant generation.
    Similar to InvariantOracle but for struct-level invariants. -/
structure StructInvariantOracle (σ : Type) where
  /-- Generate struct invariant suggestions. -/
  suggest : StructContext σ → List (StructInvariantSuggestion σ)

/-- Mock struct invariant oracle with hard-coded entries. -/
def mkMockStructOracle {σ : Type}
    (entries : List (String × List (StructInvariantSuggestion σ))) :
    StructInvariantOracle σ where
  suggest := fun ctx =>
    match entries.find? (fun e => e.1 == ctx.structName) with
    | some (_, suggestions) => suggestions
    | none => []

/-! # Verification: struct invariant must be preserved by all operations -/

/-- Check that a struct invariant is preserved by all operations.
    This uses the preserves_invariant_unconditional from GlobalInvariant.lean.

    For each operation, we need:
    - If the invariant holds before the operation
    - Then it holds after the operation (for all result states) -/
def checkStructInvariant {σ : Type}
    (inv : GlobalInvariant σ) (ops : List (String × L1Monad σ)) :
    List (String × Prop) :=
  ops.map fun (name, body) =>
    (name, preserves_invariant_unconditional inv body)

/-- A struct invariant is valid when all operations preserve it. -/
def structInvariantValid {σ : Type}
    (inv : GlobalInvariant σ) (ops : List (String × L1Monad σ)) : Prop :=
  ∀ op, op ∈ ops → preserves_invariant_unconditional inv op.2

/-! # Soundness theorem -/

/-- If a struct invariant is valid (preserved by all operations),
    then any sequence of operations preserves it.

    This is the struct-level analog of while_invariant_rule:
    the AI proposes the invariant, and the kernel checks that
    every operation preserves it. -/
theorem struct_invariant_seq {σ : Type}
    (inv : GlobalInvariant σ)
    (ops : List (String × L1Monad σ))
    (h_valid : structInvariantValid inv ops)
    (m₁ m₂ : L1Monad σ)
    (h₁_name : String) (h₂_name : String)
    (h₁_mem : (h₁_name, m₁) ∈ ops) (h₂_mem : (h₂_name, m₂) ∈ ops) :
    preserves_invariant_unconditional inv (L1.seq m₁ m₂) :=
  preserves_seq inv m₁ m₂ (h_valid _ h₁_mem) (h_valid _ h₂_mem)

/-! # Common invariant patterns

These are patterns that an LLM would typically suggest for common
data structure shapes. The mock oracle uses these. -/

/-- Pattern: bounded counter invariant.
    For any struct with a count and capacity field. -/
def boundedCounterInv {σ : Type} (getCount : σ → Nat) (getCap : σ → Nat) : GlobalInvariant σ :=
  fun s => getCount s ≤ getCap s ∧ getCap s > 0

/-- Pattern: null-consistency invariant.
    A pointer is null iff a count is zero. -/
def nullConsistencyInv {σ : Type} (isNull : σ → Prop) (isZero : σ → Prop)
    [DecidablePred isNull] [DecidablePred isZero] : GlobalInvariant σ :=
  fun s => isNull s ↔ isZero s

/-- Pattern: combined invariant from multiple sub-invariants.
    An LLM might propose several independent constraints;
    we compose them with conjunction. -/
def combinedInvariant {σ : Type} (invs : List (GlobalInvariant σ)) : GlobalInvariant σ :=
  fun s => ∀ inv, inv ∈ invs → inv s

/-- Simpler form: conjunction of exactly two invariants. -/
def conjInvariant {σ : Type} (inv₁ inv₂ : GlobalInvariant σ) : GlobalInvariant σ :=
  fun s => inv₁ s ∧ inv₂ s

/-- If both sub-invariants are preserved, the conjunction is preserved. -/
theorem conjInvariant_preserved {σ : Type}
    (inv₁ inv₂ : GlobalInvariant σ) (body : L1Monad σ)
    (h₁ : preserves_invariant_unconditional inv₁ body)
    (h₂ : preserves_invariant_unconditional inv₂ body) :
    preserves_invariant_unconditional (conjInvariant inv₁ inv₂) body :=
  preserves_conjunction inv₁ inv₂ body h₁ h₂

/-! # Metrics for struct invariant generation -/

/-- Track struct invariant generation metrics. -/
structure StructAIMetrics where
  /-- Total struct contexts processed -/
  totalStructs : Nat
  /-- Invariants accepted (all ops preserve) -/
  accepted : Nat
  /-- Invariants rejected (some op violates) -/
  rejected : Nat
  /-- Per-operation preservation success count -/
  opsChecked : Nat
  /-- Per-operation preservation failure count -/
  opsFailed : Nat

def StructAIMetrics.successRate (m : StructAIMetrics) : Float :=
  if m.totalStructs == 0 then 0.0
  else Float.ofNat m.accepted / Float.ofNat m.totalStructs * 100.0

def StructAIMetrics.toString (m : StructAIMetrics) : String :=
  s!"Struct AI Metrics: {m.accepted}/{m.totalStructs} structs ({m.successRate}%), " ++
  s!"{m.opsChecked - m.opsFailed}/{m.opsChecked} ops preserved"

instance : ToString StructAIMetrics := ⟨StructAIMetrics.toString⟩
