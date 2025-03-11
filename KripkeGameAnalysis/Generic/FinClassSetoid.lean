import Mathlib.Data.Finset.Basic

class FinClassSetoid (α : Type) extends Setoid α where
  enumerateClass: α → Finset α
  enumerateClass_mem_iff: ∀ x y, x ∈ enumerateClass y ↔ x ≈ y

namespace FinClassSetoid

lemma enumerateClass_self_mem [FinClassSetoid α] (x : α) : x ∈ enumerateClass x :=
  (FinClassSetoid.enumerateClass_mem_iff x x).mpr (Setoid.refl x)

theorem enumerateClass_eq [FinClassSetoid α] (x y : α) : enumerateClass x = enumerateClass y ↔ x ≈ y := by
  apply Iff.intro
  · intro h
    have x_mem_enumerateClass_y : x ∈ enumerateClass y := by rw [←h]; exact enumerateClass_self_mem x
    exact (enumerateClass_mem_iff x y).mp x_mem_enumerateClass_y
  · intro h
    ext a
    apply Iff.intro
    · intro h'
      apply (enumerateClass_mem_iff _ _).mpr
      apply (enumerateClass_mem_iff _ _).mp at h'
      exact (Setoid.iseqv.trans h' h)
    · intro h'
      apply (enumerateClass_mem_iff _ _).mpr
      apply (enumerateClass_mem_iff _ _).mp at h'
      exact (Setoid.iseqv.trans h' (Setoid.iseqv.symm h))

instance instEquivDecidable [FinClassSetoid α] [DecidableEq α] : DecidableRel ((· ≈ ·): α → α → Prop) := fun x y =>
  decidable_of_decidable_of_iff (FinClassSetoid.enumerateClass_mem_iff x y)

end FinClassSetoid
