-- AI-assisted specification drafting framework
--
-- Given a C function's signature, types, and comments, an AI drafts
-- a FuncSpec (precondition + postcondition). The human reviews and
-- the Lean kernel checks.
--
-- This addresses the "spec writing" bottleneck. As de Moura describes:
-- "reading the formal statement and saying yes, this is what I meant,
-- remains the human job." AI drafts, humans validate.
--
-- Common patterns the AI applies:
-- - Pointer parameters -> heapPtrValid in precondition
-- - Return value -> constraint in postcondition
-- - Array parameters + size -> bounds in precondition
-- - Struct parameters -> field constraints
-- - Read-only functions -> state unchanged in postcondition
--
-- Reference: task-0101

import Clift.Lifting.FuncSpec
import Clift.Lifting.L1HoareRules
import Clift.AI.InvariantGen

/-! # Function signature representation -/

/-- C type categories relevant to spec generation. -/
inductive CTypeCategory where
  | scalar     -- int, unsigned, etc.
  | pointer    -- T* (pointer to T)
  | struct     -- struct S
  | void       -- void return
  | array      -- T[] or T* used as array

/-- A parameter description: what the AI sees about each parameter. -/
structure ParamInfo where
  /-- Parameter name -/
  name : String
  /-- C type as a string (e.g., "uint32_t *") -/
  cType : String
  /-- Type category -/
  category : CTypeCategory
  /-- Whether the parameter is const-qualified -/
  isConst : Bool

/-- Function signature context for spec generation. -/
structure FuncSigContext where
  /-- Function name -/
  funcName : String
  /-- Parameters -/
  params : List ParamInfo
  /-- Return type -/
  returnType : ParamInfo
  /-- Doc comments from the C source -/
  docComment : Option String
  /-- Whether the function modifies the heap (has non-const pointer params) -/
  modifiesHeap : Bool

/-! # Spec suggestion -/

/-- A suggested specification for a function. -/
structure SpecSuggestion (σ : Type) where
  /-- The suggested FuncSpec -/
  spec : FuncSpec σ
  /-- Human-readable description of precondition -/
  preDescription : String
  /-- Human-readable description of postcondition -/
  postDescription : String
  /-- Confidence level (0.0 to 1.0) -/
  confidence : Float

/-! # Spec oracle: the AI interface -/

/-- A spec oracle generates FuncSpec suggestions from function signatures.
    This is the interface for AI-assisted spec drafting. -/
structure SpecOracle (σ : Type) where
  /-- Generate spec suggestions for a function. -/
  suggest : FuncSigContext → List (SpecSuggestion σ)

/-- Mock spec oracle with hard-coded entries. -/
def mkMockSpecOracle {σ : Type}
    (entries : List (String × List (SpecSuggestion σ))) :
    SpecOracle σ where
  suggest := fun ctx =>
    match entries.find? (fun e => e.1 == ctx.funcName) with
    | some (_, suggestions) => suggestions
    | none => []

/-! # Spec generation rules: pattern-based precondition generation

These rules capture common C verification patterns. An LLM would
learn these from examples; the mock oracle uses them directly. -/

/-- Rule: pointer parameters require heapPtrValid.
    For every non-null pointer parameter, add heapPtrValid to the precondition. -/
def pointerParamNames (ctx : FuncSigContext) : List String :=
  (ctx.params.filter fun p => match p.category with
    | .pointer => true
    | _ => false).map ParamInfo.name

/-- Rule: const pointer parameters mean read-only (heap unchanged in post).
    If all pointer params are const, the heap should be unchanged. -/
def isReadOnly (ctx : FuncSigContext) : Bool :=
  ctx.params.all fun p => match p.category with
    | .pointer => p.isConst
    | _ => true

/-- Rule: void return means no return value constraint needed. -/
def hasReturnValue (ctx : FuncSigContext) : Bool :=
  match ctx.returnType.category with
  | .void => false
  | _ => true

/-! # Spec validation -/

/-- A spec suggestion can be checked against a function body.
    If validHoare holds, the spec is valid. -/
def validateSpec {σ : Type} (spec : FuncSpec σ) (body : L1Monad σ) : Prop :=
  spec.satisfiedBy body

/-- Spec validation result. -/
inductive SpecCheckResult where
  /-- Spec validated: body satisfies the spec -/
  | valid
  /-- Spec too strong: precondition does not guarantee postcondition -/
  | tooStrong (failingObligation : String)
  /-- Spec too weak: precondition does not exclude enough bad inputs -/
  | tooWeak (counterexample : String)

/-! # Human review workflow

The AI-assisted spec workflow:

1. AI sees FuncSigContext (signature, types, comments)
2. AI generates List (SpecSuggestion sigma) ordered by confidence
3. Human reviews each suggestion:
   a. Accept: use as-is
   b. Modify: edit pre/post, AI refines
   c. Reject: AI tries next suggestion
4. Accepted spec is checked by Lean kernel (validHoare proof)

The human review step is ESSENTIAL. Unlike invariants (which can be
mechanically checked via VCs), specs define WHAT the function should do.
Only a human can decide if a spec captures the intended behavior.

The value of AI: drafting saves time. The human validates, not creates. -/

/-- Record of a human review decision. -/
inductive ReviewDecision where
  /-- Accept the spec as-is -/
  | accept
  /-- Modify the spec (human provides edited version) -/
  | modify
  /-- Reject and try next suggestion -/
  | reject (reason : String)

/-! # Metrics -/

/-- Track spec generation metrics. -/
structure SpecAIMetrics where
  /-- Total functions processed -/
  totalFunctions : Nat
  /-- Specs accepted on first suggestion -/
  acceptedFirst : Nat
  /-- Specs accepted after modification -/
  acceptedModified : Nat
  /-- Specs rejected (human wrote from scratch) -/
  rejected : Nat

def SpecAIMetrics.acceptanceRate (m : SpecAIMetrics) : Float :=
  if m.totalFunctions == 0 then 0.0
  else Float.ofNat (m.acceptedFirst + m.acceptedModified) / Float.ofNat m.totalFunctions * 100.0

def SpecAIMetrics.firstShotRate (m : SpecAIMetrics) : Float :=
  if m.totalFunctions == 0 then 0.0
  else Float.ofNat m.acceptedFirst / Float.ofNat m.totalFunctions * 100.0

def SpecAIMetrics.toString (m : SpecAIMetrics) : String :=
  s!"Spec AI Metrics: {m.acceptedFirst + m.acceptedModified}/{m.totalFunctions} accepted " ++
  s!"({m.acceptanceRate}%), {m.acceptedFirst} first-shot ({m.firstShotRate}%)"

instance : ToString SpecAIMetrics := ⟨SpecAIMetrics.toString⟩
