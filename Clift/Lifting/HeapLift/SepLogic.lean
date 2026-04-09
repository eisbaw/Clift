-- Basic separation logic predicates: mapsTo, sep (separating conjunction), frame rule
--
-- Reference: ext/AutoCorres2/Split_Heap.thy
-- Reference: ext/tuch-types-bytes-seplogic-popl2007.pdf
-- Reference: plan.md Decision 9
--
-- We define separation logic predicates over the raw heap (HeapRawState)
-- at the pointer level. The "footprint" of a predicate is the set of
-- pointer addresses it asserts about. Separating conjunction requires
-- disjoint footprints.
--
-- Design choice: we work directly with HeapRawState and typed pointers,
-- not with split heaps. This keeps things simple for Phase 3 — the
-- predicates are independent of the split heap abstraction.

import Clift.Lifting.HeapLift.SimpleLift
import Clift.MonadLib.Hoare

/-! # HeapPred: predicates over heap states -/

/-- A heap predicate is a proposition about the raw heap state. -/
def HeapPred := HeapRawState → Prop

/-! # mapsTo: pointer points to a specific value -/

/-- `mapsTo p v h` asserts that pointer `p` is valid in heap `h` and
    the value at `p` is `v`. This is the fundamental "points-to" predicate
    of separation logic, written `p ↦ v` in standard notation.

    Following AutoCorres: validity includes type tag match, non-null,
    and in-bounds. -/
def mapsTo {α : Type} [MemType α] (p : Ptr α) (v : α) : HeapPred :=
  fun h => heapPtrValid h p ∧ hVal h p = v

/-! # emp: empty heap assertion -/

/-- `emp` holds for any heap state. It asserts nothing about the heap.
    In standard sep logic, emp asserts the heap is empty. Here, since
    we don't track a "domain" explicitly, emp is True.

    Note: this is a simplification. A more precise version would track
    which addresses are "owned" by the assertion. For Phase 3, the
    simpler version suffices because we use ptrDisjoint for separation. -/
def emp : HeapPred := fun _ => True

/-! # Separating conjunction

    `sep P Q h` asserts that both P and Q hold on the heap h, and their
    "footprints" are disjoint. Since we don't have explicit footprint
    tracking (that would require a more complex domain model), we
    parameterize sep over an explicit disjointness witness.

    For Phase 3, we define a concrete version for mapsTo predicates
    where disjointness is expressed via ptrDisjoint. -/

/-- Separating conjunction for two mapsTo predicates.
    `sepMapsTo p vp q vq h` asserts:
    - p ↦ vp
    - q ↦ vq
    - p and q have disjoint byte ranges -/
def sepMapsTo {α β : Type} [CType α] [MemType α] [CType β] [MemType β]
    (p : Ptr α) (vp : α) (q : Ptr β) (vq : β) : HeapPred :=
  fun h => mapsTo p vp h ∧ mapsTo q vq h ∧ ptrDisjoint p q

/-- General separating conjunction: both predicates hold and an
    explicit disjointness side condition is satisfied.
    The side condition `disj` captures that the resources claimed
    by P and Q do not overlap. -/
def sep (P Q : HeapPred) (disj : HeapRawState → Prop) : HeapPred :=
  fun h => P h ∧ Q h ∧ disj h

/-! # sep_comm: P * Q ↔ Q * P -/

theorem sepMapsTo_comm {α β : Type} [CType α] [MemType α] [CType β] [MemType β]
    {p : Ptr α} {vp : α} {q : Ptr β} {vq : β} {h : HeapRawState} :
    sepMapsTo p vp q vq h ↔ sepMapsTo q vq p vp h := by
  unfold sepMapsTo
  constructor
  · intro ⟨hp, hq, hdisj⟩; exact ⟨hq, hp, ptrDisjoint_symm hdisj⟩
  · intro ⟨hq, hp, hdisj⟩; exact ⟨hp, hq, ptrDisjoint_symm hdisj⟩

theorem sep_comm {P Q : HeapPred} {disj : HeapRawState → Prop}
    (h_symm : ∀ h, disj h → disj h)  -- disj is symmetric
    {h : HeapRawState} :
    sep P Q disj h ↔ sep Q P disj h := by
  unfold sep
  constructor
  · intro ⟨hp, hq, hd⟩; exact ⟨hq, hp, h_symm h hd⟩
  · intro ⟨hq, hp, hd⟩; exact ⟨hp, hq, h_symm h hd⟩

/-! # sep_assoc for mapsTo triples

    For three mapsTo predicates, associativity holds with pairwise disjointness. -/

/-- Three-way mapsTo separation: all three point-to hold with pairwise disjointness. -/
def sepMapsTo3 {α β γ : Type} [CType α] [MemType α] [CType β] [MemType β] [CType γ] [MemType γ]
    (p : Ptr α) (vp : α) (q : Ptr β) (vq : β) (r : Ptr γ) (vr : γ) : HeapPred :=
  fun h => mapsTo p vp h ∧ mapsTo q vq h ∧ mapsTo r vr h ∧
           ptrDisjoint p q ∧ ptrDisjoint p r ∧ ptrDisjoint q r

/-- sep_assoc: nesting two-way separating conjunctions is equivalent to
    three-way pairwise disjoint conjunction. This is the associativity
    property for concrete mapsTo predicates. -/
theorem sepMapsTo_assoc {α β γ : Type}
    [CType α] [MemType α] [CType β] [MemType β] [CType γ] [MemType γ]
    {p : Ptr α} {vp : α} {q : Ptr β} {vq : β} {r : Ptr γ} {vr : γ}
    {h : HeapRawState} :
    (sepMapsTo p vp q vq h ∧ mapsTo r vr h ∧ ptrDisjoint p r ∧ ptrDisjoint q r) ↔
    sepMapsTo3 p vp q vq r vr h := by
  unfold sepMapsTo sepMapsTo3
  constructor
  · intro ⟨⟨hp, hq, hdpq⟩, hr, hdpr, hdqr⟩
    exact ⟨hp, hq, hr, hdpq, hdpr, hdqr⟩
  · intro ⟨hp, hq, hr, hdpq, hdpr, hdqr⟩
    exact ⟨⟨hp, hq, hdpq⟩, hr, hdpr, hdqr⟩

/-! # Frame reasoning for swap

    The frame property for swap: updating pointers a and b only affects
    their values; all other valid disjoint pointers are unchanged. -/

/-- Frame theorem for simpleUpdate: if q is valid and disjoint from p,
    then updating p does not change what simpleLift sees at q.
    This is just simpleLift_update_disjoint restated at the HeapPred level. -/
theorem mapsTo_frame_update {α β : Type} [MemType α] [MemType β]
    (h : HeapRawState) (p : Ptr α) (v : α) (q : Ptr β) (vq : β)
    (h_mt : mapsTo q vq h)
    (h_disj : ptrDisjoint p q) :
    mapsTo q vq (simpleUpdate h p v) := by
  unfold mapsTo at *
  obtain ⟨hv_q, hval_q⟩ := h_mt
  constructor
  · exact heapUpdate_preserves_heapPtrValid h p v q hv_q
  · unfold simpleUpdate
    have hbq := heapPtrValid_bound hv_q
    by_cases hbp : p.addr.val + @CType.size α _ ≤ memSize
    · exact hVal_heapUpdate_disjoint h p q v hbp hbq h_disj ▸ hval_q
    · simp only [heapUpdate, dif_neg hbp]; exact hval_q

/-- After swap (two updates), a disjoint pointer r is unchanged. -/
theorem mapsTo_frame_swap {α β γ : Type} [MemType α] [MemType β] [MemType γ]
    (h : HeapRawState) (pa : Ptr α) (va : α) (pb : Ptr β) (vb : β)
    (pr : Ptr γ) (vr : γ)
    (h_mt : mapsTo pr vr h)
    (h_disj_a : ptrDisjoint pa pr)
    (h_disj_b : ptrDisjoint pb pr) :
    mapsTo pr vr (simpleUpdate (simpleUpdate h pa va) pb vb) := by
  apply mapsTo_frame_update
  · exact mapsTo_frame_update h pa va pr vr h_mt h_disj_a
  · exact h_disj_b

/-! # General frame rule for validHoare with separation

    The true separation logic frame rule says: if {P} m {Q} and m is
    "local" (only touches resources described by P), then
    {P * R} m {Q * R} for any R about disjoint resources.

    In our setting, NondetM computations don't have a built-in locality
    notion. We state the frame rule with an explicit locality hypothesis:
    the computation preserves any mapsTo assertion about a disjoint pointer.

    This is the standard approach when separation logic is layered on top
    of a state monad without substructural typing. -/

/-- Frame rule for validHoare with mapsTo separation.
    If a computation satisfies {P} m {Q} and preserves any disjoint pointer's
    mapsTo assertion (the locality hypothesis), then we can frame in
    additional mapsTo facts.

    The `h_local` hypothesis says: if pointer `q` is valid and disjoint from
    the computation's footprint, then the computation preserves `mapsTo q vq`.
    This must be proven for each specific computation (e.g., for heap updates,
    it follows from `mapsTo_frame_update`).

    This bridges the gap between our raw-heap frame lemmas and Hoare-level
    reasoning. -/
theorem validHoare_frame_mapsTo {α β : Type} [MemType β]
    {P : HeapRawState → Prop} {Q : α → HeapRawState → Prop}
    {m : NondetM HeapRawState α}
    {q : Ptr β} {vq : β}
    (h_spec : validHoare P m Q)
    (h_local : ∀ s₀, P s₀ → mapsTo q vq s₀ →
      ∀ r s₁, (r, s₁) ∈ (m s₀).results → mapsTo q vq s₁) :
    validHoare (fun s => P s ∧ mapsTo q vq s) m
               (fun r s => Q r s ∧ mapsTo q vq s) := by
  intro s₀ ⟨h_P, h_mt⟩
  have ⟨h_nf, h_post⟩ := h_spec s₀ h_P
  exact ⟨h_nf, fun r s₁ h_mem =>
    ⟨h_post r s₁ h_mem, h_local s₀ h_P h_mt r s₁ h_mem⟩⟩

/-- Iterated frame rule: frame in two disjoint mapsTo assertions. -/
theorem validHoare_frame_sepMapsTo {α β γ : Type} [CType β] [MemType β] [CType γ] [MemType γ]
    {P : HeapRawState → Prop} {Q : α → HeapRawState → Prop}
    {m : NondetM HeapRawState α}
    {q : Ptr β} {vq : β} {r : Ptr γ} {vr : γ}
    (h_spec : validHoare P m Q)
    (h_local_q : ∀ s₀, P s₀ → mapsTo q vq s₀ → mapsTo r vr s₀ →
      ∀ rv s₁, (rv, s₁) ∈ (m s₀).results → mapsTo q vq s₁)
    (h_local_r : ∀ s₀, P s₀ → mapsTo q vq s₀ → mapsTo r vr s₀ →
      ∀ rv s₁, (rv, s₁) ∈ (m s₀).results → mapsTo r vr s₁)
    (h_disj : ptrDisjoint q r) :
    validHoare (fun s => P s ∧ sepMapsTo q vq r vr s) m
               (fun rv s => Q rv s ∧ sepMapsTo q vq r vr s) := by
  intro s₀ ⟨h_P, h_sep⟩
  have ⟨h_mt_q, h_mt_r, _⟩ := h_sep
  have ⟨h_nf, h_post⟩ := h_spec s₀ h_P
  exact ⟨h_nf, fun rv s₁ h_mem =>
    ⟨h_post rv s₁ h_mem,
     h_local_q s₀ h_P h_mt_q h_mt_r rv s₁ h_mem,
     h_local_r s₀ h_P h_mt_q h_mt_r rv s₁ h_mem,
     h_disj⟩⟩

/-! # Swap correctness at the simpleLift level -/

/-- After updating p with value v, mapsTo p v holds on the new heap.
    Requires p to be valid in the original heap. -/
theorem mapsTo_after_update {α : Type} [MemType α]
    (h : HeapRawState) (p : Ptr α) (v : α)
    (hv : heapPtrValid h p) :
    mapsTo p v (simpleUpdate h p v) := by
  unfold mapsTo simpleUpdate
  constructor
  · exact heapUpdate_preserves_heapPtrValid h p v p hv
  · exact hVal_heapUpdate_same h p v (heapPtrValid_bound hv)

/-- Swap spec at the separation logic level:
    Given {mapsTo a va * mapsTo b vb} (i.e., a ↦ va, b ↦ vb, disjoint),
    after updating a := vb then b := va,
    we get {mapsTo a vb * mapsTo b va}. -/
theorem swap_sep_correct {α : Type} [MemType α]
    (h : HeapRawState) (a b : Ptr α) (va vb : α)
    (h_pre : sepMapsTo a va b vb h) :
    sepMapsTo a vb b va (simpleUpdate (simpleUpdate h a vb) b va) := by
  obtain ⟨h_ma, h_mb, h_disj⟩ := h_pre
  obtain ⟨hva, hvala⟩ := h_ma
  obtain ⟨hvb, hvalb⟩ := h_mb
  unfold sepMapsTo
  refine ⟨?_, ?_, h_disj⟩
  · -- After update a := vb, update b := va: show a ↦ vb
    apply mapsTo_frame_update
    · -- After first update, a ↦ vb
      exact mapsTo_after_update h a vb hva
    · -- b is disjoint from a
      exact ptrDisjoint_symm h_disj
  · -- After update a := vb, update b := va: show b ↦ va
    apply mapsTo_after_update
    · -- b is valid in the intermediate heap (after updating a)
      exact heapUpdate_preserves_heapPtrValid h a vb b hvb
