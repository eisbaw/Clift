-- L5Auto: MetaM automation for WordAbstract (UInt32 -> Nat)
--
-- Given a pure L3 function operating on UInt32 values, help the user
-- prove correspondence with a Nat-level function.
--
-- Phase A approach (annotated MetaM):
--   The user provides the Nat-level function definition.
--   clift_wa generates the WAcorres proof obligation and attempts
--   to discharge it using wordToNat lemmas + simp + omega.
--
-- For simple arithmetic functions (no overflow), the proof is often
-- automatic. For functions with while loops, user may need to provide
-- the induction argument.
--
-- Reference: ext/AutoCorres2/word_abstract.ML
-- Reference: Clift/Lifting/WordAbstract.lean (WAcorres definitions)
-- Reference: Examples/GcdWordAbstract.lean (manual L5 for gcd)

import Clift.Lifting.WordAbstract
import Lean

open Lean Meta Elab Command Term Tactic

/-! # WAcorres for unary and ternary pure functions -/

/-- WAcorres for unary pure functions. -/
def WAcorres_pure1
    (f_word : UInt32 → UInt32)
    (f_nat : Nat → Nat)
    (guard : Nat → Prop) : Prop :=
  ∀ a : UInt32,
    guard (wordToNat a) →
    wordToNat (f_word a) = f_nat (wordToNat a)

/-- WAcorres for ternary pure functions. -/
def WAcorres_pure3
    (f_word : UInt32 → UInt32 → UInt32 → UInt32)
    (f_nat : Nat → Nat → Nat → Nat)
    (guard : Nat → Nat → Nat → Prop) : Prop :=
  ∀ a b c : UInt32,
    guard (wordToNat a) (wordToNat b) (wordToNat c) →
    wordToNat (f_word a b c) = f_nat (wordToNat a) (wordToNat b) (wordToNat c)

/-! # Tactic: wa_simp — simplify wordToNat goals

Applies all wordToNat correspondence lemmas and tries omega. -/

/-- `wa_simp` tactic: simplify word abstraction goals using
    wordToNat lemmas, then try omega for remaining arithmetic. -/
macro "wa_simp" : tactic =>
  `(tactic| (
    simp only [wordToNat, wordToNat_mod, wordToNat_add,
               wordToNat_zero, wordToNat_eq_iff,
               UInt32.toNat_mod]
    <;> try omega))

/-! # clift_wa: command to generate and prove WAcorres

Usage:
  clift_wa <word_fn> <nat_fn>
  clift_wa <word_fn> <nat_fn> <guard_fn>

Generates:
  theorem <word_fn>_wa : WAcorres_pure[N] <word_fn> <nat_fn> <guard>

The command inspects the arity to choose WAcorres_pure1/2/3.
If no guard is provided, uses `fun _ => True` (or `fun _ _ => True`).

The proof is attempted by:
1. intro + simp with wordToNat lemmas
2. omega for arithmetic
3. If that fails, the obligation is left for the user
-/

/-- Generate a trivial guard (fun args => True) for the given arity. -/
private def mkTrueGuard (arity : Nat) : MetaM Expr := do
  let natType := .const ``Nat []
  let trueVal := .const ``True []
  match arity with
  | 1 => return .lam `_ natType trueVal .default
  | 2 => return .lam `_ natType (.lam `_ natType trueVal .default) .default
  | 3 => return .lam `_ natType (.lam `_ natType (.lam `_ natType trueVal .default) .default) .default
  | _ => throwError "mkTrueGuard: unsupported arity {arity}"

elab "clift_wa " wordFn:ident natFn:ident : command => do
  let wordName := wordFn.getId
  let natName := natFn.getId

  liftTermElabM do
    let env ← getEnv
    unless env.contains wordName do
      throwError "clift_wa: {wordName} not found"
    unless env.contains natName do
      throwError "clift_wa: {natName} not found"

    let wordRef := Lean.mkConst wordName
    let wordType ← inferType wordRef
    let natRef := Lean.mkConst natName

    -- Count arity by counting UInt32 parameters
    let mut ty := wordType
    let mut arity : Nat := 0
    while ty.isForall do
      let dom := ty.bindingDomain!
      if dom.isConstOf ``UInt32 then
        arity := arity + 1
      ty := ty.bindingBody!

    let guard ← mkTrueGuard arity

    -- Build WAcorres type
    let corresConst := match arity with
      | 1 => ``WAcorres_pure1
      | 2 => ``WAcorres_pure2
      | 3 => ``WAcorres_pure3
      | _ => ``WAcorres_pure2  -- fallback
    let corresType := mkApp3 (.const corresConst []) wordRef natRef guard

    let thmName := wordName.getPrefix ++ Name.mkSimple s!"{wordName.components.getLast!}_wa"

    -- Try to prove by tactic
    let proof ← mkFreshExprMVar corresType
    let mvarId := proof.mvarId!

    let goals ← Tactic.run mvarId do
      -- Unfold the WAcorres definition and introduce all forall'd variables
      evalTactic (← `(tactic| unfold $(mkIdent corresConst)))
      -- Introduce all universally quantified variables
      for _ in List.range (arity + 1) do  -- arity args + 1 guard hypothesis
        evalTactic (← `(tactic| intro _))
      -- Unfold the word and nat function definitions
      evalTactic (← `(tactic| unfold $(mkIdent wordName) $(mkIdent natName)))
      evalTactic (← `(tactic| wa_simp))

    if goals.isEmpty then
      let proofVal ← instantiateMVars proof
      addDecl <| Declaration.thmDecl {
        name := thmName
        levelParams := []
        type := corresType
        value := proofVal
      }
      logInfo m!"clift_wa: {thmName} proved (WAcorres arity={arity})"
    else
      logWarning m!"clift_wa: could not auto-prove WAcorres for {wordName} -> {natName} ({goals.length} goals remaining). Manual proof needed."
      -- Still add the type as an axiom-free declaration would require sorry
      -- Instead, report what's needed
      for g in goals do
        let goalTy ← g.getType
        logWarning m!"  Remaining goal: {goalTy}"
