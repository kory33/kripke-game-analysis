import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

class FinClassSetoid (α : Type) [Setoid α] where
  enumerateClass: α → Finset α
  enumerateClass_mem_iff: ∀ x y, x ∈ enumerateClass y ↔ x ≈ y
namespace FinClassSetoid

lemma enumerateClass_self_mem [Setoid α] [FinClassSetoid α] (x : α) : x ∈ enumerateClass x :=
  (FinClassSetoid.enumerateClass_mem_iff x x).mpr (Setoid.refl x)

theorem enumerateClass_eq [Setoid α] [FinClassSetoid α] (x y : α) : enumerateClass x = enumerateClass y ↔ x ≈ y := by
  apply Iff.intro
  · intro h
    have x_mem_enumerateClass_y : x ∈ enumerateClass y := by rw [←h]; exact enumerateClass_self_mem x
    exact (enumerateClass_mem_iff x y).mp x_mem_enumerateClass_y
  · intro h
    ext a
    repeat rw [enumerateClass_mem_iff]
    exact ⟨(Setoid.trans · h), (Setoid.trans · (Setoid.symm h))⟩

instance instEquivDecidable [Setoid α] [FinClassSetoid α] [DecidableEq α] : DecidableRel ((· ≈ ·): α → α → Prop) := fun x y =>
  decidable_of_decidable_of_iff (FinClassSetoid.enumerateClass_mem_iff x y)

end FinClassSetoid
