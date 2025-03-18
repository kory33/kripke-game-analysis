import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fin.Basic

namespace Fin

def finMulEquivMulFin {n m : Nat} : (Fin n) × (Fin m) ≃ Fin (n * m) :=
  have fin_implies_gt_zero {k : Nat} : Fin k → k > 0 := fun i => by
    have : k ≠ 0 := by intro h; rw [h] at i; exact Nat.not_lt_zero _ i.is_lt
    exact Nat.pos_of_ne_zero this

  have product_fin_implies_right_gt_zero {n m : Nat} : Fin (n * m) → (m > 0) := fun i => by
    have prod_gt_zero : n * m > 0 := fin_implies_gt_zero i
    revert prod_gt_zero; contrapose!; simp only [Nat.le_zero_eq]
    intro h; rw [h]; simp
  {
    toFun := fun ⟨i, j⟩ => ⟨
      i.val * m + j.val, by
      calc
        i.val * m + j.val
          < i.val * m + m     := Nat.add_lt_add_left j.is_lt _
        _ = (i.val + 1) * m   := by rw [Nat.right_distrib, Nat.one_mul]
        _ ≤ n * m             := Nat.mul_le_mul_right m (Nat.succ_le_of_lt i.is_lt)
    ⟩,
    invFun := fun p => ⟨
      ⟨
        p.val / m, by
          apply (Nat.div_lt_iff_lt_mul _).mpr
          · exact p.is_lt
          · exact product_fin_implies_right_gt_zero p
      ⟩,
      ⟨
        p.val % m, by
          exact Nat.mod_lt _ (product_fin_implies_right_gt_zero p)
      ⟩
    ⟩,
    left_inv := fun ⟨a, b⟩ => by
      suffices _ : ((a * m + b) / m = a) ∧ (b % m = b) by
        simp only [Nat.mul_add_mod_self_right, Prod.mk.injEq]
        apply And.intro
        · apply Fin.eq_of_val_eq; dsimp only; tauto
        · apply Fin.eq_of_val_eq; dsimp only; tauto

      apply And.intro
      · calc
          (a * m + b) / m
            = a + b / m         := by rw [Nat.mul_comm _ _, Nat.mul_add_div (fin_implies_gt_zero b)]
          _ = a                 := by rw [Nat.div_eq_of_lt b.is_lt, Nat.add_zero]
      · exact Nat.mod_eq_of_lt b.is_lt
    ,
    right_inv := fun ⟨a, b⟩ => by
      simp only [mk.injEq]
      rw [Nat.add_comm, Nat.mul_comm, Nat.mod_add_div _ _]
  }

end Fin
