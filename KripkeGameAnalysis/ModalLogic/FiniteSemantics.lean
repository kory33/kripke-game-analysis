import Init.Data.BitVec.Basic
import Mathlib.Data.Nat.Cast.Order.Basic

import KripkeGameAnalysis.ModalLogic.Basic
import KripkeGameAnalysis.GenericExtras.BitVec

/--
A finite Kripke frame is a Kripke frame with a finite number of vertices.
We think of the vertices in the Kripke frame as being numbered from `0` to `frameSize - 1`, inclusive.
-/
def FiniteKripkeFrame (frameSize : Nat) : Type := KripkeFrame (Fin frameSize)

@[ext] lemma FiniteKripkeFrame.ext
  {frameSize : Nat} {frame1 frame2 : FiniteKripkeFrame frameSize}
  (h : ∀i j, frame1 i j = frame2 i j) : frame1 = frame2 :=
  funext (λ i => funext (λ j => h i j))

namespace FiniteKripkeFrame
  instance (frame : FiniteKripkeFrame n) : Fintype frame.vertices := inferInstanceAs (Fintype (Fin n))
  instance (frame : FiniteKripkeFrame n) : DecidableEq frame.vertices := inferInstanceAs (DecidableEq (Fin n))

  def allNodes (frame : FiniteKripkeFrame n) : Finset frame.vertices := Finset.univ
  lemma allNodes_card_eq_frameSize (frame : FiniteKripkeFrame n) : frame.allNodes.card = n :=
    by apply Fintype.card_fin

  def accessibilityRelationCount (frame : FiniteKripkeFrame n) : ℕ :=
    ((frame.allNodes.product (frame.allNodes)).filter (fun a => frame.accessible a.fst a.snd)).card

  section FiniteValuation
  structure FiniteValuation (frame : FiniteKripkeFrame n) (finVars : Type) [Fintype finVars] [DecidableEq finVars] where
    valuation : frame.Valuation finVars

  variable {finVars : Type} [Fintype finVars] [DecidableEq finVars]
  namespace FiniteValuation
    def equivToFinSetRepresentation {frame : FiniteKripkeFrame n}:
                                    (frame.FiniteValuation finVars) ≃ (Finset (finVars × frame.vertices)) :=
      let valPowersetEquiv : (frame.Valuation finVars) ≃ (Finset (finVars × frame.vertices)) := finsetProdEquivCurriedCharacteristic.symm
      let valEquiv : (frame.FiniteValuation finVars) ≃ (frame.Valuation finVars) := {
        toFun := fun val => val.valuation,
        invFun := fun val => { valuation := val },
        left_inv := by intro val; simp,
        right_inv := by intro val; simp
      }
      valEquiv.trans valPowersetEquiv
  end FiniteValuation

  def allFinValuations (frame : FiniteKripkeFrame n) : Finset (frame.FiniteValuation finVars) :=
    let valuationsAsPsets := (Finset.product (inferInstance (α := Fintype finVars)).elems frame.allNodes).powerset
    valuationsAsPsets.map (FiniteValuation.equivToFinSetRepresentation (frame := frame).symm.toEmbedding)

  def satisfiesForAllValuations {frame : FiniteKripkeFrame n} (i : frame.vertices) (fml : ModalFormula finVars) : Bool :=
    decide (∀finval ∈ frame.allFinValuations, finval.valuation.decideSatisfaction i fml)

  def countSatisfyingNodes (frame : FiniteKripkeFrame n) (fml : ModalFormula finVars) : ℕ :=
    (frame.allNodes.filter (fun i => satisfiesForAllValuations i fml)).card

  lemma countSatisfyingNodes_leq_frameSize: ∀ {frame : FiniteKripkeFrame n} {fml : ModalFormula finVars},
                                             frame.countSatisfyingNodes fml ≤ n := by
    intro frame fml
    simp only [FiniteKripkeFrame.countSatisfyingNodes]
    simp only [← frame.allNodes_card_eq_frameSize]
    apply Finset.card_filter_le
  end FiniteValuation

  def equivSquareBoolFn : (FiniteKripkeFrame n) ≃ (Fin (n ^ 2) → Bool) :=
    let fin_implies_gt_zero {k : Nat} : Fin k → k > 0 := fun i => by
      have : k ≠ 0 := by intro h; rw [h] at i; exact Nat.not_lt_zero _ i.is_lt
      exact Nat.pos_of_ne_zero this

    let frameToBoolFn : (FiniteKripkeFrame n) → (Fin (n ^ 2) → Bool) := fun frame i =>
      let n_gt_zero : n > 0 := by
        have n_sq_gt_zero : n ^ 2 > 0 := fin_implies_gt_zero i
        have : n ^ 2 > 0 → n > 0 := by contrapose; simp
        exact this n_sq_gt_zero

      frame
        ⟨i.val / n, by apply (Nat.div_lt_iff_lt_mul n_gt_zero).mpr; rw [←Nat.pow_two n]; exact i.is_lt⟩
        ⟨i.val % n, by exact Nat.mod_lt _ n_gt_zero⟩

    let boolFnToFrame : (Fin (n ^ 2) → Bool) → (FiniteKripkeFrame n) := fun boolFn i j =>
      boolFn
        ⟨i.val * n + j.val, by
          simp [Nat.pow_two]
          calc
            i.val * n + j.val
              < i.val * n + n    := Nat.add_lt_add_left j.is_lt (i.val * n)
            _ = (i.val + 1) * n  := by rw [Nat.right_distrib, Nat.one_mul]
            _ ≤ n * n            := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.is_lt)
        ⟩

    {
      toFun := frameToBoolFn,
      invFun := boolFnToFrame,
      left_inv := by
        intro frame
        simp [frameToBoolFn, boolFnToFrame]; simp [FiniteKripkeFrame, KripkeFrame] at frame
        ext i j; congr
        · calc
            (↑i * n + ↑j) / n
              = (n * ↑i + ↑j) / n := by rw [Nat.mul_comm _ _]
            _ = ↑i + ↑j / n       := by rw [Nat.mul_add_div (fin_implies_gt_zero i) i j]
            _ = ↑i                := by rw [Nat.div_eq_of_lt j.is_lt]; simp
        · exact Nat.mod_eq_of_lt j.is_lt,
      right_inv := by
        intro boolFn
        simp [frameToBoolFn, boolFnToFrame]
        ext i; congr
        rw [Nat.add_comm, Nat.mul_comm, Nat.mod_add_div _ _]
    }

  def UptoIso (n : Nat) := Quotient (KripkeFrame.isSetoid (Fin n))
end FiniteKripkeFrame

def FiniteKripkeFrameBitVecRepr (frameSize : Nat) : Type := BitVec (frameSize ^ 2)
namespace FiniteKripkeFrameBitVecRepr
  def equiv: (FiniteKripkeFrame n) ≃ (FiniteKripkeFrameBitVecRepr n) :=
    FiniteKripkeFrame.equivSquareBoolFn.trans (BitVec.equivToBitPred (n ^ 2)).symm

  instance : Fintype (FiniteKripkeFrameBitVecRepr n) := inferInstanceAs (Fintype (BitVec (n ^ 2)))
end FiniteKripkeFrameBitVecRepr

namespace FiniteKripkeFrame
  instance : Fintype (FiniteKripkeFrame n) :=
    Fintype.ofEquiv (FiniteKripkeFrameBitVecRepr n) FiniteKripkeFrameBitVecRepr.equiv.symm
end FiniteKripkeFrame
