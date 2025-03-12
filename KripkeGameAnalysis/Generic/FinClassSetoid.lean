import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

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

instance instQuotDecidableEq [s : FinClassSetoid α] [DecidableEq α] : DecidableEq (Quotient s.toSetoid) := fun x y =>
  let x_elem_enumerateClass_y := x.liftOn (Quotient.mk s.toSetoid · = y) (
    by
    intro a b h; simp
    have qa_eq_qb : Quotient.mk s.toSetoid a = Quotient.mk s.toSetoid b := Quot.sound h
    rw [qa_eq_qb]
  )
  if h : decide (x_elem_enumerateClass_y) then
    Decidable.isTrue (by
      simp [x_elem_enumerateClass_y] at h
      revert h
      apply Quotient.inductionOn x (motive := _)
      intro a h
      rw [Quotient.liftOn_mk] at h
      assumption
    )
  else
    Decidable.isFalse (by
      simp [x_elem_enumerateClass_y] at h
      intro h'
      apply h
      revert h'
      apply Quotient.inductionOn x (motive := _)
      intro a h
      rw [Quotient.liftOn_mk]
      assumption
    )

end FinClassSetoid
