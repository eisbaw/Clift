-- Minimal Set definition and lemmas for Clift.
--
-- Replaces Mathlib.Data.Set.Basic to avoid 9GB+ RAM per Lean process.
-- Set α is just α → Prop. We provide only what our codebase actually uses.
--
-- If you need more Set lemmas, add them here rather than pulling in Mathlib.

universe u

/-! # Set definition -/

/-- A set of elements of type α, represented as a predicate.
    Using `abbrev` so the kernel can freely unfold `Set α` to `α → Prop`. -/
abbrev Set (α : Type u) := α → Prop

namespace Set

variable {α : Type u}

/-! # Membership

Note: In Lean 4.30+, Membership.mem has signature `γ → α → Prop` (container first).
So `mem s a := s a` means: given set s and element a, check s a. -/

instance : Membership α (Set α) where
  mem s a := s a

/-! # Empty set -/

instance : EmptyCollection (Set α) where
  emptyCollection := fun _ => False

@[simp] theorem mem_empty_iff {a : α} : a ∈ (∅ : Set α) ↔ False := Iff.rfl

theorem not_mem_empty (a : α) : a ∉ (∅ : Set α) := id

/-! # Singleton -/

instance : Singleton α (Set α) where
  singleton a := fun x => x = a

@[simp] theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl

/-! # Insert (needed for {a, b, ...} notation) -/

instance : Insert α (Set α) where
  insert a s := fun x => x = a ∨ s x

@[simp] theorem mem_insert_iff {a b : α} {s : Set α} :
    a ∈ (Insert.insert b s : Set α) ↔ a = b ∨ a ∈ s := Iff.rfl

/-! # Union -/

instance : Union (Set α) where
  union s t := fun x => s x ∨ t x

@[simp] theorem mem_union {a : α} {s t : Set α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := Iff.rfl

theorem mem_union_left {a : α} {s : Set α} (t : Set α) (h : a ∈ s) : a ∈ s ∪ t :=
  Or.inl h

theorem mem_union_right {a : α} (s : Set α) {t : Set α} (h : a ∈ t) : a ∈ s ∪ t :=
  Or.inr h

/-! # Extensionality -/

@[ext] theorem ext {s t : Set α} (h : ∀ (a : α), a ∈ s ↔ a ∈ t) : s = t :=
  funext fun a => propext (h a)

end Set
