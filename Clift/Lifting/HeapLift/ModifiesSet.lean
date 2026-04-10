-- ModifiesSet: semantic modifies-set analysis for frame reasoning
--
-- A computation "modifies at most S" if every heap location outside S
-- is unchanged in every result state, and the heap type descriptor (htd)
-- is preserved. This enables the frame rule: if m modifies at most S,
-- and pointer p is valid and its footprint is outside S, then mapsTo p v
-- is preserved by m.
--
-- Design choice: semantic property (not syntactic analysis).
-- The semantic approach composes naturally with L1 combinators and
-- avoids needing MetaM for syntactic tree walking.
--
-- Reference: AutoCorres2's modifies_spec

import Clift.Lifting.HeapLift.SepLogic
import Clift.Lifting.L1HoareRules

/-! # HeapLocSet and pointer footprints -/

/-- A set of heap byte addresses. -/
abbrev HeapLocSet := Set (Fin memSize)

/-- The byte footprint of a typed pointer: the set of addresses
    [addr, addr + size). -/
def ptrFootprint {α : Type} [CType α] (p : Ptr α) : HeapLocSet :=
  fun a => p.addr.val ≤ a.val ∧ a.val < p.addr.val + CType.size (α := α)

/-- A pointer is outside a location set if no byte in its footprint is in the set. -/
def ptrOutside {α : Type} [CType α] (p : Ptr α) (S : HeapLocSet) : Prop :=
  ∀ (a : Fin memSize), a ∈ S →
    ¬(p.addr.val ≤ a.val ∧ a.val < p.addr.val + CType.size (α := α))

/-- If p is outside S and q's footprint is in S, then q and p are disjoint. -/
theorem ptrOutside_ptrDisjoint {α β : Type} [CType α] [CType β]
    (p : Ptr α) (q : Ptr β) (S : HeapLocSet)
    (h_out : ptrOutside p S)
    (h_in : ∀ a : Fin memSize,
      q.addr.val ≤ a.val ∧ a.val < q.addr.val + CType.size (α := β) → a ∈ S) :
    ptrDisjoint q p := by
  unfold ptrDisjoint
  -- Proof by contradiction: assume there's overlap, derive False
  suffices h : ¬(q.addr.val + CType.size (α := β) ≤ p.addr.val) →
    ¬(p.addr.val + CType.size (α := α) ≤ q.addr.val) → False by
    by_cases h1 : q.addr.val + CType.size (α := β) ≤ p.addr.val
    · exact Or.inl h1
    · by_cases h2 : p.addr.val + CType.size (α := α) ≤ q.addr.val
      · exact Or.inr h2
      · exact (h h1 h2).elim
  intro h1 h2
  -- There's overlap between q and p byte ranges
  by_cases hle : q.addr.val ≤ p.addr.val
  · -- p.addr is in q's range
    have hp_in_q : q.addr.val ≤ p.addr.val ∧ p.addr.val < q.addr.val + CType.size (α := β) :=
      ⟨hle, by omega⟩
    have hp_in_S := h_in ⟨p.addr.val, p.addr.isLt⟩ hp_in_q
    have hp_in_p : p.addr.val ≤ p.addr.val ∧ p.addr.val < p.addr.val + CType.size (α := α) :=
      ⟨Nat.le_refl _, by have := CType.size_pos (α := α); omega⟩
    exact h_out ⟨p.addr.val, p.addr.isLt⟩ hp_in_S hp_in_p
  · -- q.addr is in p's range
    have hq_in_q : q.addr.val ≤ q.addr.val ∧ q.addr.val < q.addr.val + CType.size (α := β) :=
      ⟨Nat.le_refl _, by have := CType.size_pos (α := β); omega⟩
    have hq_in_S := h_in ⟨q.addr.val, q.addr.isLt⟩ hq_in_q
    have hq_in_p : p.addr.val ≤ q.addr.val ∧ q.addr.val < p.addr.val + CType.size (α := α) :=
      ⟨by omega, by omega⟩
    exact h_out ⟨q.addr.val, q.addr.isLt⟩ hq_in_S hq_in_p

/-! # modifiesHeapOnly: the core semantic modifies-set property -/

/-- A NondetM computation preserves the heap type descriptor everywhere
    and only modifies memory within S.

    This is the semantic counterpart of a "modifies set" declaration.
    Every L1 combinator gets a composition lemma for this property. -/
def modifiesHeapOnly {α : Type} (m : NondetM HeapRawState α) (S : HeapLocSet) : Prop :=
  ∀ (s₀ : HeapRawState) (r : α) (s₁ : HeapRawState),
    (r, s₁) ∈ (m s₀).results →
    (∀ (a : Fin memSize), a ∉ S → s₁.mem a = s₀.mem a) ∧
    s₁.htd = s₀.htd

/-! # modifiesHeapOnly for L1 combinators -/

theorem modifiesHeapOnly_skip :
    modifiesHeapOnly (α := Except Unit Unit) L1.skip ∅ := by
  intro s₀ r s₁ h_mem
  have heq := (Prod.mk.inj h_mem).2
  subst heq
  exact ⟨fun _ _ => rfl, rfl⟩

theorem modifiesHeapOnly_throw :
    modifiesHeapOnly (α := Except Unit Unit) L1.throw ∅ := by
  intro s₀ r s₁ h_mem
  have heq := (Prod.mk.inj h_mem).2
  subst heq
  exact ⟨fun _ _ => rfl, rfl⟩

theorem modifiesHeapOnly_guard (p : HeapRawState → Prop) [DecidablePred p] :
    modifiesHeapOnly (L1.guard p) ∅ := by
  intro s₀ r s₁ h_mem
  by_cases hp : p s₀
  · rw [L1_guard_results hp] at h_mem
    have heq := (Prod.mk.inj h_mem).2
    subst heq
    exact ⟨fun _ _ => rfl, rfl⟩
  · have : (L1.guard p s₀).results = ∅ := by
      show (if p s₀ then _ else (⟨∅, True⟩ : NondetResult HeapRawState _)).results = ∅
      rw [if_neg hp]
    rw [this] at h_mem; exact absurd h_mem (Set.not_mem_empty _)

theorem modifiesHeapOnly_modify (f : HeapRawState → HeapRawState) (S : HeapLocSet)
    (h_mem_f : ∀ s a, a ∉ S → (f s).mem a = s.mem a)
    (h_htd_f : ∀ s, (f s).htd = s.htd) :
    modifiesHeapOnly (L1.modify f) S := by
  intro s₀ r s₁ h_res
  have heq := (Prod.mk.inj h_res).2
  subst heq
  exact ⟨fun a ha => h_mem_f s₀ a ha, h_htd_f s₀⟩

theorem modifiesHeapOnly_seq (m₁ m₂ : L1Monad HeapRawState) (S₁ S₂ : HeapLocSet)
    (h₁ : modifiesHeapOnly m₁ S₁) (h₂ : modifiesHeapOnly m₂ S₂) :
    modifiesHeapOnly (L1.seq m₁ m₂) (S₁ ∪ S₂) := by
  intro s₀ r s₁ h_mem
  change (_ ∨ _) at h_mem
  rcases h_mem with ⟨s', h_m1, h_m2⟩ | ⟨h_err, _⟩
  · have ⟨hmem1, hhtd1⟩ := h₁ s₀ (Except.ok ()) s' h_m1
    have ⟨hmem2, hhtd2⟩ := h₂ s' r s₁ h_m2
    constructor
    · intro a ha
      have ha1 : a ∉ S₁ := fun h => ha (Or.inl h)
      have ha2 : a ∉ S₂ := fun h => ha (Or.inr h)
      rw [hmem2 a ha2, hmem1 a ha1]
    · rw [hhtd2, hhtd1]
  · have ⟨hmem1, hhtd1⟩ := h₁ s₀ (Except.error ()) s₁ h_err
    constructor
    · intro a ha
      have ha1 : a ∉ S₁ := fun h => ha (Or.inl h)
      exact hmem1 a ha1
    · exact hhtd1

theorem modifiesHeapOnly_catch (body handler : L1Monad HeapRawState) (S₁ S₂ : HeapLocSet)
    (h₁ : modifiesHeapOnly body S₁) (h₂ : modifiesHeapOnly handler S₂) :
    modifiesHeapOnly (L1.catch body handler) (S₁ ∪ S₂) := by
  intro s₀ r s₁ h_mem
  change (_ ∨ _) at h_mem
  rcases h_mem with ⟨h_ok, _⟩ | ⟨s', h_err, h_handler⟩
  · have ⟨hmem1, hhtd1⟩ := h₁ s₀ (Except.ok ()) s₁ h_ok
    constructor
    · intro a ha
      have ha1 : a ∉ S₁ := fun h => ha (Or.inl h)
      exact hmem1 a ha1
    · exact hhtd1
  · have ⟨hmem1, hhtd1⟩ := h₁ s₀ (Except.error ()) s' h_err
    have ⟨hmem2, hhtd2⟩ := h₂ s' r s₁ h_handler
    constructor
    · intro a ha
      have ha1 : a ∉ S₁ := fun h => ha (Or.inl h)
      have ha2 : a ∉ S₂ := fun h => ha (Or.inr h)
      rw [hmem2 a ha2, hmem1 a ha1]
    · rw [hhtd2, hhtd1]

/-! # Frame theorem from modifiesHeapOnly -/

/-- Frame theorem: if m preserves htd and only modifies memory in S,
    and pointer q has its footprint outside S, then mapsTo q vq is preserved.

    This is the main payoff of modifies-set analysis. -/
theorem modifiesHeapOnly_frame_mapsTo {α β : Type} [instB : MemType β]
    (m : NondetM HeapRawState α) (S : HeapLocSet)
    (q : Ptr β) (vq : β)
    (h_mod : modifiesHeapOnly m S)
    (h_out : ptrOutside q S) :
    ∀ (s₀ : HeapRawState), mapsTo q vq s₀ →
      ∀ r s₁, (r, s₁) ∈ (m s₀).results → mapsTo q vq s₁ := by
  intro s₀ h_mt r s₁ h_mem
  have ⟨h_mem_eq, h_htd_eq⟩ := h_mod s₀ r s₁ h_mem
  unfold mapsTo at h_mt ⊢
  obtain ⟨hv, hval⟩ := h_mt
  constructor
  · -- heapPtrValid preserved
    unfold heapPtrValid at hv ⊢
    obtain ⟨hbound, hnonnull, halign, htag⟩ := hv
    refine ⟨hbound, hnonnull, halign, ?_⟩
    intro i hi
    have h_htd_i := htag i hi
    -- htd is preserved globally
    have : s₁.htd = s₀.htd := h_htd_eq
    simp only [this]
    exact h_htd_i
  · -- hVal preserved: all bytes in q's footprint are unchanged
    unfold hVal readMemSlice at hval ⊢
    rw [← hval]
    congr 1
    funext ⟨i, hi⟩
    have hbound := heapPtrValid_bound hv
    have h_no_wrap : (q.addr.val + i) % memSize = q.addr.val + i :=
      Nat.mod_eq_of_lt (by omega)
    apply h_mem_eq
    intro h_in_S
    -- If this address is in S, then it's also in ptrFootprint q
    -- But ptrOutside says no address in S is in ptrFootprint q
    have h_in_foot : q.addr.val ≤ ((q.addr.val + i) % memSize) ∧
        ((q.addr.val + i) % memSize) < q.addr.val + CType.size (α := β) := by
      rw [h_no_wrap]; exact ⟨by omega, by omega⟩
    exact h_out _ h_in_S h_in_foot

/-! # heapUpdate modifies only the pointer's footprint -/

/-- heapUpdate preserves htd. -/
theorem heapUpdate_preserves_htd' {α : Type} [MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α) :
    (heapUpdate h p v).htd = h.htd := by
  unfold heapUpdate
  split
  · simp [heapUpdate']
  · rfl

/-- heapUpdate only changes memory within the pointer's byte range. -/
theorem heapUpdate_mem_outside {α : Type} [instA : MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α)
    (a : Fin memSize)
    (h_out : ¬(p.addr.val ≤ a.val ∧ a.val < p.addr.val + instA.size)) :
    (heapUpdate h p v).mem a = h.mem a := by
  unfold heapUpdate
  by_cases hb : p.addr.val + instA.size ≤ memSize
  · rw [dif_pos hb]
    unfold heapUpdate' writeMemSlice
    simp only
    rw [dif_neg h_out]
  · rw [dif_neg hb]

/-- L1.modify with heapUpdate modifies only the pointer's footprint. -/
theorem heapUpdate_modifiesHeapOnly {α : Type} [instA : MemType α]
    (p : Ptr α) (v : α) :
    modifiesHeapOnly (L1.modify (fun h => heapUpdate h p v)) (ptrFootprint p) := by
  apply modifiesHeapOnly_modify
  · intro s a h_out
    exact heapUpdate_mem_outside s p v a h_out
  · intro s
    exact heapUpdate_preserves_htd' s p v

/-! # Monotonicity: modifiesHeapOnly S → S ⊆ T → modifiesHeapOnly T -/

theorem modifiesHeapOnly_mono {α : Type} {m : NondetM HeapRawState α} {S T : HeapLocSet}
    (h : modifiesHeapOnly m S) (h_sub : ∀ a, a ∈ S → a ∈ T) :
    modifiesHeapOnly m T := by
  intro s₀ r s₁ h_mem
  have ⟨hmem, hhtd⟩ := h s₀ r s₁ h_mem
  exact ⟨fun a ha => hmem a (fun h_in_S => ha (h_sub a h_in_S)), hhtd⟩

/-! # Application: swap modifies at most {footprint(a) ∪ footprint(b)}

This can be proved by composing modifiesHeapOnly_seq, modifiesHeapOnly_guard,
modifiesHeapOnly_catch, and heapUpdate_modifiesHeapOnly.
Users prove specific functions' modifies-sets as theorems. -/
