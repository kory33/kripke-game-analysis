import Init.Data.BitVec.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

namespace BitVec
  instance : Fintype (BitVec n) where
    elems := Finset.univ (α := Fin (2 ^ n)).map ⟨BitVec.ofFin, by intros _ _ _; injections⟩
    complete := by intro _; rw [Finset.mem_map]; simp

  def mkFromBitPred (n : Nat): (Fin n → Bool) -> BitVec n := fun f =>
    let upcastSuccFinFnToFinFn {k : Nat} {α : Type} (f : Fin (k + 1) → α) : Fin k → α := fun i =>
      f ⟨i.val, Nat.lt_of_lt_of_le i.is_lt (Nat.le_succ _)⟩
    match n with
    | 0 => BitVec.nil
    | k + 1 => BitVec.cons (f ⟨k, Nat.lt_succ_self k⟩) (mkFromBitPred k (upcastSuccFinFnToFinFn f))

  @[simp] lemma mkFromBitPred_get (n : Nat) (f : Fin n → Bool) (i : Fin n) : (mkFromBitPred n f)[i.val] = f i := by
    induction n with
    | zero => have i_lt_zero := i.is_lt; contradiction
    | succ n ih =>
      simp only [mkFromBitPred]; rw [BitVec.getElem_cons]
      split
      · next h =>
        have i_eq : i = ⟨n, ?_⟩ := Fin.eq_of_val_eq h
        rw [i_eq]; exact Nat.lt_succ_self n
      · next h =>
        have i_lt_n : i.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.is_lt) h
        rw [ih _ ⟨i.val, i_lt_n⟩];

  def equivToBitPred (n : Nat) : BitVec n ≃ (Fin n → Bool) :=
    {
      toFun := fun v i => v[i],
      invFun := mkFromBitPred n,
      left_inv := by
        intro v; unfold mkFromBitPred
        induction n with
        | zero => ext _ h; contradiction
        | succ n ih =>
          ext i hi; simp only
          rw [BitVec.getElem_cons hi]
          by_cases h : i = n
          · simp [h]
          · have i_lt_n : i < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) h
            simp [h, mkFromBitPred_get _ _ ⟨i, i_lt_n⟩]
      right_inv := by intro f; ext i; simp
    }
end BitVec
