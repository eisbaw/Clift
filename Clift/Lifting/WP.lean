-- Weakest precondition calculus for L1 monadic programs
--
-- Given a postcondition Q and a program c, wp(c, Q) computes the weakest
-- precondition P such that {P} c {Q}. This is the standard VCG technique.
--
-- For while loops, the user must supply an invariant I. The wp generates
-- the verification conditions: I ∧ cond → wp(body, I) and I ∧ ¬cond → Q.
--
-- Reference: seL4's NonDetMonadVCG.thy
-- Reference: plan.md Phase 4 automation

import Clift.Lifting.L1HoareRules

/-! # Weakest Precondition type

The wp maps a postcondition to a precondition. We define it for each
L1 combinator. -/

section WP

variable {σ : Type}

/-! ## wp for individual L1 combinators -/

/-- wp for L1.skip: postcondition must hold for ok in initial state. -/
def wp_skip (Q : Except Unit Unit → σ → Prop) : σ → Prop :=
  fun s => Q (Except.ok ()) s

/-- wp for L1.modify f: postcondition must hold at (f s). -/
def wp_modify (f : σ → σ) (Q : Except Unit Unit → σ → Prop) : σ → Prop :=
  fun s => Q (Except.ok ()) (f s)

/-- wp for L1.guard p: predicate must hold AND postcondition must hold. -/
def wp_guard (p : σ → Prop) (Q : Except Unit Unit → σ → Prop) : σ → Prop :=
  fun s => p s ∧ Q (Except.ok ()) s

/-- wp for L1.throw: postcondition must hold for error in initial state. -/
def wp_throw (Q : Except Unit Unit → σ → Prop) : σ → Prop :=
  fun s => Q (Except.error ()) s

/-- wp for L1.seq m₁ m₂: wp of m₁ with intermediate condition being wp of m₂.
    The intermediate condition handles both ok (continue to m₂) and error (propagate). -/
def wp_seq (wp₁ : (Except Unit Unit → σ → Prop) → σ → Prop)
    (wp₂ : (Except Unit Unit → σ → Prop) → σ → Prop)
    (Q : Except Unit Unit → σ → Prop) : σ → Prop :=
  wp₁ (fun r s => match r with
    | Except.ok () => wp₂ Q s
    | Except.error () => Q (Except.error ()) s)

/-- wp for L1.catch body handler: body must establish intermediate condition;
    ok results pass through, error results enter handler. -/
def wp_catch (wp_body : (Except Unit Unit → σ → Prop) → σ → Prop)
    (wp_handler : (Except Unit Unit → σ → Prop) → σ → Prop)
    (Q : Except Unit Unit → σ → Prop) : σ → Prop :=
  wp_body (fun r s => match r with
    | Except.ok () => Q (Except.ok ()) s
    | Except.error () => wp_handler Q s)

/-- wp for L1.while with user-supplied invariant I.
    Generates verification conditions:
    - Precondition implies invariant: P → I
    - Invariant maintained by body: I ∧ cond → wp(body, I')
      where I' requires ok → I, error → Q
    - Invariant + ¬cond implies postcondition: I ∧ ¬cond → Q

    Since the while wp requires an invariant, this is a function from
    invariant to the wp. The user supplies the invariant when calling. -/
def wp_while (cond : σ → Bool) (wp_body : (Except Unit Unit → σ → Prop) → σ → Prop)
    (inv : σ → Prop)
    (Q : Except Unit Unit → σ → Prop) : σ → Prop :=
  fun s => inv s ∧
    -- VC1: invariant maintained by body when condition holds
    (∀ s', inv s' → cond s' = true → wp_body (fun r s'' => match r with
      | Except.ok () => inv s''
      | Except.error () => Q (Except.error ()) s'') s') ∧
    -- VC2: invariant + ¬cond implies postcondition
    (∀ s', inv s' → cond s' = false → Q (Except.ok ()) s')

/-! ## Soundness theorems: wp c Q implies validHoare (wp c Q) c Q -/

/-- wp_skip is sound: {wp_skip Q} skip {Q}. -/
theorem wp_skip_sound (Q : Except Unit Unit → σ → Prop) :
    validHoare (wp_skip Q) (L1.skip (σ := σ)) Q :=
  L1_hoare_skip Q

/-- wp_modify is sound: {wp_modify f Q} modify f {Q}. -/
theorem wp_modify_sound (f : σ → σ) (Q : Except Unit Unit → σ → Prop) :
    validHoare (wp_modify f Q) (L1.modify f) Q :=
  L1_hoare_modify f Q

/-- wp_guard is sound: {wp_guard p Q} guard p {Q}. -/
theorem wp_guard_sound (p : σ → Prop) [DecidablePred p] (Q : Except Unit Unit → σ → Prop) :
    validHoare (wp_guard p Q) (L1.guard p) Q :=
  L1_hoare_guard p Q

/-- wp_throw is sound: {wp_throw Q} throw {Q}. -/
theorem wp_throw_sound (Q : Except Unit Unit → σ → Prop) :
    validHoare (wp_throw Q) (L1.throw (σ := σ)) Q := by
  intro s₀ hpre
  constructor
  · intro h; exact h
  · intro r s₁ h_mem
    have heq := Prod.mk.inj h_mem
    rw [heq.1, heq.2]; exact hpre

/-- wp_seq is sound: {wp_seq wp₁ wp₂ Q} seq m₁ m₂ {Q}
    given soundness of wp₁ and wp₂. -/
theorem wp_seq_sound (m₁ m₂ : L1Monad σ)
    (wp₁ wp₂ : (Except Unit Unit → σ → Prop) → σ → Prop)
    (h₁ : ∀ Q, validHoare (wp₁ Q) m₁ Q)
    (h₂ : ∀ Q, validHoare (wp₂ Q) m₂ Q)
    (Q : Except Unit Unit → σ → Prop) :
    validHoare (wp_seq wp₁ wp₂ Q) (L1.seq m₁ m₂) Q := by
  apply L1_hoare_seq (wp_seq wp₁ wp₂ Q) (wp₂ Q) Q m₁ m₂
  · -- m₁ with intermediate condition
    have h := h₁ (fun r s => match r with
      | Except.ok () => wp₂ Q s
      | Except.error () => Q (Except.error ()) s)
    exact h
  · exact h₂ Q

/-- wp_catch is sound. -/
theorem wp_catch_sound (body handler : L1Monad σ)
    (wp_b wp_h : (Except Unit Unit → σ → Prop) → σ → Prop)
    (h_b : ∀ Q, validHoare (wp_b Q) body Q)
    (h_h : ∀ Q, validHoare (wp_h Q) handler Q)
    (Q : Except Unit Unit → σ → Prop) :
    validHoare (wp_catch wp_b wp_h Q) (L1.catch body handler) Q := by
  apply L1_hoare_catch (wp_catch wp_b wp_h Q) (wp_h Q) Q body handler
  · exact h_b _
  · exact h_h Q

/-- wp_while is sound: if the user supplies a valid invariant,
    then {wp_while cond wp_body inv Q} while cond body {Q}. -/
theorem wp_while_sound (cond : σ → Bool) (body : L1Monad σ)
    (wp_body : (Except Unit Unit → σ → Prop) → σ → Prop)
    (inv : σ → Prop)
    (h_body : ∀ Q, validHoare (wp_body Q) body Q)
    (Q : Except Unit Unit → σ → Prop) :
    validHoare (wp_while cond wp_body inv Q) (L1.while cond body) Q := by
  intro s₀ ⟨h_inv, h_vc1, h_vc2⟩
  -- Key: we prove both no-failure and postcondition simultaneously
  -- by showing that inv holds at every state reachable in the while loop.
  -- Auxiliary lemma: inv at any reachable state implies the while spec
  suffices aux : ∀ s, inv s →
    (∀ s', inv s' → cond s' = true → wp_body (fun r s'' => match r with
      | Except.ok () => inv s''
      | Except.error () => Q (Except.error ()) s'') s') →
    (∀ s', inv s' → cond s' = false → Q (Except.ok ()) s') →
    ¬(L1.while cond body s).failed ∧
    ∀ r s₁, (r, s₁) ∈ (L1.while cond body s).results → Q r s₁ from
    aux s₀ h_inv h_vc1 h_vc2
  intro s h_inv_s h_vc1' h_vc2'
  constructor
  · -- No failure
    intro hf
    suffices h_aux : ∀ s', L1.WhileFail cond body s' → inv s' → False from
      h_aux s hf h_inv_s
    intro s'
    intro hf'
    -- induction on WhileFail, generalizing over inv hypothesis
    induction hf'
    case here s_cur hc hf_body =>
      intro h_inv'
      exact (h_body _ s_cur (h_vc1' s_cur h_inv' hc)).1 hf_body
    case later s_cur s_next hc h_ok _h_rest ih =>
      intro h_inv'
      have h_spec := h_body _ s_cur (h_vc1' s_cur h_inv' hc)
      have h_post := h_spec.2 (Except.ok ()) s_next h_ok
      exact ih h_post
  · -- Postcondition
    intro r s₁ h_mem
    suffices h_aux : ∀ s' (p : Except Unit Unit × σ), L1.WhileResult cond body s' p →
        inv s' → Q p.1 p.2 from
      h_aux s (r, s₁) h_mem h_inv_s
    intro s' p hr
    induction hr
    case done s_cur hc =>
      intro h_inv'
      exact h_vc2' s_cur h_inv' hc
    case step s_cur s_next p' hc h_ok _h_rest ih =>
      intro h_inv'
      have h_spec := h_body _ s_cur (h_vc1' s_cur h_inv' hc)
      have h_post := h_spec.2 (Except.ok ()) s_next h_ok
      exact ih h_post
    case abrupt s_cur s_exit hc h_err =>
      intro h_inv'
      have h_spec := h_body _ s_cur (h_vc1' s_cur h_inv' hc)
      exact h_spec.2 (Except.error ()) s_exit h_err

/-! ## Convenience: combined wp computation

A wp "program" computes the wp for a compound L1 program. -/

/-- wp for a compound L1 program expressed as a function from postcondition
    to precondition. Sound if used correctly with the composition lemmas above. -/
structure WPSpec (σ : Type) where
  /-- The L1 program -/
  prog : L1Monad σ
  /-- The wp transformer -/
  wp : (Except Unit Unit → σ → Prop) → σ → Prop
  /-- Soundness proof -/
  sound : ∀ Q, validHoare (wp Q) prog Q

/-- Build a WPSpec for skip. -/
def WPSpec.ofSkip : WPSpec σ where
  prog := L1.skip
  wp := wp_skip
  sound := wp_skip_sound

/-- Build a WPSpec for modify. -/
def WPSpec.ofModify (f : σ → σ) : WPSpec σ where
  prog := L1.modify f
  wp := wp_modify f
  sound := wp_modify_sound f

/-- Build a WPSpec for guard. -/
def WPSpec.ofGuard (p : σ → Prop) [DecidablePred p] : WPSpec σ where
  prog := L1.guard p
  wp := wp_guard p
  sound := wp_guard_sound p

/-- Build a WPSpec for throw. -/
def WPSpec.ofThrow : WPSpec σ where
  prog := L1.throw
  wp := wp_throw
  sound := wp_throw_sound

/-- Sequence two WPSpecs. -/
def WPSpec.seq (s1 s2 : WPSpec σ) : WPSpec σ where
  prog := L1.seq s1.prog s2.prog
  wp := wp_seq s1.wp s2.wp
  sound := wp_seq_sound s1.prog s2.prog s1.wp s2.wp s1.sound s2.sound

/-- Catch with WPSpecs. -/
def WPSpec.catch (body handler : WPSpec σ) : WPSpec σ where
  prog := L1.catch body.prog handler.prog
  wp := wp_catch body.wp handler.wp
  sound := wp_catch_sound body.prog handler.prog body.wp handler.wp body.sound handler.sound

end WP
