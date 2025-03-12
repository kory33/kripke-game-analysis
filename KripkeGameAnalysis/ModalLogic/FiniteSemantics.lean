import Init.Data.BitVec.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Insert

import KripkeGameAnalysis.Generic.FinClassSetoid
import KripkeGameAnalysis.Generic.SetoidWithCanonicalizer
import KripkeGameAnalysis.GenericExtras.BitVec
import KripkeGameAnalysis.ModalLogic.Basic

/--
A finite Kripke frame is a Kripke frame with a finite number of vertices.
We think of the vertices in the Kripke frame as being numbered from `0` to `frameSize - 1`, inclusive.

We use a `BitVec` to represent the accessibility relation of the Kripke frame.
The `BitVec` is of size `frameSize ^ 2`, and the bit at position `i * frameSize + j` is `true`
if there is an edge from vertex `i` to vertex `j`, and `false` otherwise.
-/
def FiniteKripkeFrame (frameSize : Nat) : Type := BitVec (frameSize ^ 2)

namespace FiniteKripkeFrame
  def mk (n : ℕ) (v : BitVec (n ^ 2)) : FiniteKripkeFrame n := v

  def kripkeFrameFinNEquivSquareBoolFn : KripkeFrame (Fin n) ≃ (Fin (n ^ 2) → Bool) :=
    let fin_implies_gt_zero {k : Nat} : Fin k → k > 0 := fun i => by
      have : k ≠ 0 := by intro h; rw [h] at i; exact Nat.not_lt_zero _ i.is_lt
      exact Nat.pos_of_ne_zero this

    let frameToBoolFn : KripkeFrame (Fin n) → (Fin (n ^ 2) → Bool) := fun frame i =>
      let n_gt_zero : n > 0 := by
        have n_sq_gt_zero : n ^ 2 > 0 := fin_implies_gt_zero i
        have : n ^ 2 > 0 → n > 0 := by contrapose; simp
        exact this n_sq_gt_zero

      frame
        ⟨i.val / n, by apply (Nat.div_lt_iff_lt_mul n_gt_zero).mpr; rw [←Nat.pow_two n]; exact i.is_lt⟩
        ⟨i.val % n, by exact Nat.mod_lt _ n_gt_zero⟩

    let boolFnToFrame : (Fin (n ^ 2) → Bool) → KripkeFrame (Fin n) := fun boolFn i j =>
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

  def equivToKripkeFrameFin: FiniteKripkeFrame n ≃ KripkeFrame (Fin n) :=
    (BitVec.equivToBitPred (n ^ 2)).trans kripkeFrameFinNEquivSquareBoolFn.symm

  instance instLinOrd : LinearOrder (FiniteKripkeFrame n) where
    le := fun f1 f2 => (f1 : BitVec (n ^ 2)).ule f2
    le_refl := by intro f; simp [BitVec.ule]
    le_trans := by intro f1 f2 f3; simp [BitVec.ule]; exact Nat.le_trans
    le_antisymm := by intro f1 f2; simp [BitVec.ule]; intro h1 h2; apply BitVec.eq_of_toNat_eq; apply Nat.le_antisymm h1 h2
    le_total := by intro f1 f2; simp [BitVec.ule]; exact Nat.le_total _ _
    decidableLE := fun f1 f2 => inferInstanceAs (Decidable ((f1 : BitVec (n ^ 2)).ule f2))
  instance instCoe : Coe (FiniteKripkeFrame n) (KripkeFrame (Fin n)) where coe := equivToKripkeFrameFin.toFun
  abbrev asKripkeFrame (frame : FiniteKripkeFrame n) : KripkeFrame (Fin n) := frame
  instance instFunLike : FunLike (FiniteKripkeFrame n) (Fin n) (Fin n → Bool) where
    coe frame := frame.asKripkeFrame
    coe_injective' := by
      intro frame1 frame2 h
      have h' : frame1.asKripkeFrame = frame2.asKripkeFrame := h
      simp [asKripkeFrame] at h'
      exact h'
  @[simp] theorem equivToKripkeFrameFin_coe (frame : FiniteKripkeFrame n) : (equivToKripkeFrameFin frame) i j = frame i j := by rfl

  abbrev mkFromKripkeFrameFin (frame : KripkeFrame (Fin n)) : FiniteKripkeFrame n := equivToKripkeFrameFin.invFun frame
  @[simp] theorem mkFromKripkeFrameFin_coe (frame : KripkeFrame (Fin n)) : (mkFromKripkeFrameFin frame) i j = frame i j := by
    simp [mkFromKripkeFrameFin]
    have h : DFunLike.coe (equivToKripkeFrameFin.symm frame) = frame := equivToKripkeFrameFin.right_inv frame
    rw [h]
  @[ext] theorem ext {frame1 frame2 : FiniteKripkeFrame n} (h : ∀i j, frame1 i j = frame2 i j) : frame1 = frame2 :=
    instFunLike.coe_injective' (funext (λ i => funext (λ j => h i j)))

  abbrev vertices (frame : FiniteKripkeFrame n) : Type := frame.asKripkeFrame.vertices
  instance (frame : FiniteKripkeFrame n) : Fintype frame.vertices := inferInstanceAs (Fintype (Fin n))
  instance (frame : FiniteKripkeFrame n) : DecidableEq frame.vertices := inferInstanceAs (DecidableEq (Fin n))

  instance : Fintype (FiniteKripkeFrame n) := inferInstanceAs (Fintype (BitVec (n ^ 2)))
  instance : DecidableEq (FiniteKripkeFrame n) := inferInstanceAs (DecidableEq (BitVec (n ^ 2)))
  instance : Hashable (FiniteKripkeFrame n) := inferInstanceAs (Hashable (BitVec (n ^ 2)))
end FiniteKripkeFrame

namespace KripkeFrame
  instance : Fintype (KripkeFrame (Fin n)) := Fintype.ofEquiv _ FiniteKripkeFrame.equivToKripkeFrameFin
end KripkeFrame

namespace FiniteKripkeFrame
  def allNodes (frame : FiniteKripkeFrame n) : Finset frame.vertices := Finset.univ
  lemma allNodes_card_eq_frameSize (frame : FiniteKripkeFrame n) : frame.allNodes.card = n :=
    by apply Fintype.card_fin

  def accessibilityRelationCount (frame : FiniteKripkeFrame n) : ℕ :=
    let asBitVec : BitVec (n ^ 2) := frame
    (Finset.univ.filter (fun (i : Fin (n ^ 2)) => asBitVec[i])).card

  section FiniteValuation
  abbrev Valuation (frame : FiniteKripkeFrame n) (vars : Type) : Type := frame.asKripkeFrame.Valuation vars
  structure FiniteValuation (frame : FiniteKripkeFrame n) (finVars : Type) [Fintype finVars] [DecidableEq finVars] where
    valuation : frame.Valuation finVars

  variable {finVars : Type} [Fintype finVars] [DecidableEq finVars]
  namespace FiniteValuation
    def equivToFinSetRepresentation {frame : FiniteKripkeFrame n}:
                                    (frame.FiniteValuation finVars) ≃ (Finset (finVars × frame.vertices)) :=
      let valPowersetEquiv : (frame.Valuation finVars) ≃ (Finset (finVars × frame.vertices)) :=
        finsetProdEquivCurriedCharacteristic.symm
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

  section Isomorphism
  instance isSetoid (n : ℕ) : Setoid (FiniteKripkeFrame n) where
    r := fun frame1 frame2 => frame1.asKripkeFrame ≈ frame2
    iseqv := by
      constructor
      · intro frame; exact KripkeFrame.isomorphism_equivalence.refl _
      · intro frame1 frame2 h; exact KripkeFrame.isomorphism_equivalence.symm h
      · intro frame1 frame2 frame3 h1 h2; exact KripkeFrame.isomorphism_equivalence.trans h1 h2
  def UptoIso (n: ℕ) : Type := Quotient (isSetoid n)

  instance FinClassSetoid (n : ℕ) : FinClassSetoid (FiniteKripkeFrame n) where
    enumerateClass := fun f =>
      let permutateFrame : Equiv.Perm (Fin n) → FiniteKripkeFrame n := fun f' =>
        mkFromKripkeFrameFin (fun i j => f (f' i) (f' j))
      Finset.univ (α := Equiv.Perm (Fin n)).image permutateFrame
    enumerateClass_mem_iff f f' := by
      simp
      apply Iff.intro
      · intro iso_exists
        rcases iso_exists with ⟨iso, iso_prop⟩
        simp [HasEquiv.Equiv, KripkeFrame.Isomorphic]
        exists iso
        intros i j
        apply congrArg (· i j) at iso_prop; simp at iso_prop
        simp [KripkeFrame.accessible]; rw [asKripkeFrame]; simp; exact iso_prop.symm
      · intro equiv
        simp [HasEquiv.Equiv, KripkeFrame.Isomorphic] at equiv
        rcases equiv with ⟨iso, iso_prop⟩
        exists iso
        ext i j; simp; exact (iso_prop i j).symm
  abbrev enumerateClass (f : FiniteKripkeFrame n) : Finset (FiniteKripkeFrame n) := FinClassSetoid.enumerateClass f

  instance : SetoidWithCanonicalizer (FiniteKripkeFrame n) where
    canonicalize f :=
      let classOf_f := FinClassSetoid.enumerateClass f
      let nonempty : classOf_f.Nonempty := by have : f ∈ classOf_f := FinClassSetoid.enumerateClass_self_mem f; exists f
      classOf_f.min' nonempty
    canonicalize_equiv_self f := by
      simp
      set lhs := (FinClassSetoid.enumerateClass f).min' _
      have lhs_in_class_f : lhs ∈ FinClassSetoid.enumerateClass f := Finset.min'_mem _ _
      exact (FinClassSetoid.enumerateClass_mem_iff lhs f).mp lhs_in_class_f
    equiv_then_canonicalize_eq f f' := by
      intro h; simp
      have enumerateClass_f_eq := (FinClassSetoid.enumerateClass_eq f f').mpr h
      simp [enumerateClass_f_eq]
  end Isomorphism

  abbrev canonicalize (f : FiniteKripkeFrame n) : FiniteKripkeFrame n := SetoidWithCanonicalizer.canonicalize f
  theorem canonicalize_weakly_regressive : canonicalize f ≤ f := by
    simp [canonicalize]; apply Finset.min'_le _ _; exact FinClassSetoid.enumerateClass_self_mem f
  instance : DecidableEq (UptoIso n) := inferInstanceAs (DecidableEq (Quotient (isSetoid n)))

  instance : Fintype (UptoIso n) :=
    let allFramesOrdered : List (FiniteKripkeFrame n) := (List.finRange (2 ^ (n ^ 2))).map (BitVec.ofNat (n ^ 2))
    let insertIfNotSeen (seen : Std.HashSet (FiniteKripkeFrame n))
                        (frames : Finset (UptoIso n))
                        (frame : FiniteKripkeFrame n) : Finset (UptoIso n) :=
      if seen.contains frame then frames else insert (Quotient.mk' frame) frames
    let foldStep (frame : FiniteKripkeFrame n)
                 (pair : Std.HashSet (FiniteKripkeFrame n) × Finset (UptoIso n)) :=
      (pair.fst.insertMany (frame.enumerateClass.sort (· ≤ ·)), insertIfNotSeen pair.fst pair.snd frame)

    let loop_invariant (pair : Std.HashSet (FiniteKripkeFrame n) × Finset (UptoIso n)) :=
      pair.fst.toList.toFinset.image Quotient.mk' = pair.snd

    let foldStep_elem : ∀ seen accum frame,
                        loop_invariant (seen, accum) →
                        Quotient.mk' frame ∈ (foldStep frame (seen, accum)).snd := by
      intro seen accum frame invariant
      simp [foldStep, insertIfNotSeen]
      by_cases h : seen.contains frame
      · simp [h]
        simp [loop_invariant] at invariant
        rw [← invariant]
        apply Finset.mem_image.mpr
        exists frame
        simp
        exact h
      · simp [h]

    let foldStep_preserves_elem : ∀ prev frame frame',
                                  Quotient.mk' frame ∈ prev.snd →
                                  Quotient.mk' frame ∈ (foldStep frame' prev).snd := by
      intro prev frame frame' elem
      simp [foldStep, insertIfNotSeen]
      by_cases h : prev.fst.contains frame'
      · simp [h]
        exact elem
      · simp [h]
        exact Or.inr elem

    let foldStep_preserves_invariant : ∀ seen frames frame,
                             loop_invariant (seen, frames) →
                             loop_invariant (foldStep frame (seen, frames)) := by
      intro seen frames frame invariant
      simp [loop_invariant] at invariant
      simp [loop_invariant, foldStep, insertIfNotSeen]
      ext upto_iso; simp
      by_cases h : seen.contains frame
      · simp [h]
        apply Quotient.inductionOn upto_iso (motive := _)
        intro f
        apply Iff.intro
        · intro h
          rw [←invariant]
          apply Finset.mem_image.mpr
          rcases h with ⟨f', f'_in_class_f, f_eq⟩
          cases f'_in_class_f
          next f'_in_seen =>
            exists f'
            simp
            exact And.intro f'_in_seen f_eq
          next f'_in_enumerateClass =>
            exists frame
            simp
            apply And.intro
            · exact h
            · have f'_eqv_frame : f' ≈ frame := (FinClassSetoid.enumerateClass_mem_iff f' frame).mp f'_in_enumerateClass
              simp only [Quotient.mk']
              rw [← Quotient.sound f'_eqv_frame]
              simp only [Quotient.mk'] at f_eq
              exact f_eq
        · intro h
          rw [←invariant] at h; simp at h
          rcases h with ⟨f', f'_in_seen, f_eq⟩
          exists f'
          apply And.intro
          · exact Or.inl f'_in_seen
          · exact f_eq
      · simp [h]
        apply Quotient.inductionOn upto_iso (motive := _)
        intro f
        apply Iff.intro
        · intro h
          rcases h with ⟨f', f'_in_class_f, f_eq⟩
          simp only [Quotient.mk']
          simp only [Quotient.mk'] at f_eq
          rw [←invariant]
          cases f'_in_class_f
          next f'_in_seen =>
            apply Or.inr
            simp
            exists f'
          next f'_in_enumerateClass =>
            apply Or.inl
            rw [← f_eq]
            apply Quotient.sound
            exact (FinClassSetoid.enumerateClass_mem_iff f' frame).mp f'_in_enumerateClass
        · intro h
          rw [←invariant] at h; simp at h
          cases h
          next qf_eq_qframe =>
            exists frame
            apply And.intro
            · apply Or.inr
              exact FinClassSetoid.enumerateClass_self_mem frame
            · exact qf_eq_qframe.symm
          next qf_in_qseen =>
            rcases qf_in_qseen with ⟨f', f'_in_seen, f_eq⟩
            exists f'
            apply And.intro
            · apply Or.inl
              assumption
            · exact f_eq

    let foldStep_invariant : ∀ (frames : List _), loop_invariant (frames.foldr foldStep ⟨∅, ∅⟩) := by
      intro frames
      induction frames with
      | nil =>
        simp [loop_invariant]
        apply List.eq_nil_of_length_eq_zero
        rw [Std.HashSet.length_toList]
        simp
      | cons head_frame frames ih =>
        exact foldStep_preserves_invariant _ _ _ ih

    let foldStep_mem : ∀ (frames : List _) frame,
                       frame ∈ frames → Quotient.mk' frame ∈ (frames.foldr foldStep ⟨∅, ∅⟩).snd := by
      intro frames
      induction frames with
      | nil => simp
      | cons head_frame frames ih =>
        intro frame hyp
        cases hyp
        next => exact foldStep_elem _ _ _ (foldStep_invariant _)
        next frame_in_frames =>
          simp; exact foldStep_preserves_elem (frames.foldr foldStep (∅, ∅)) _ _ (ih _ frame_in_frames)
    {
      elems := (allFramesOrdered.foldr foldStep ⟨∅, ∅⟩).snd,
      complete := by
        intro fUptoIso
        rcases Quotient.exists_rep fUptoIso with ⟨f, f_eq⟩
        have f_in_allFramesOrdered : f ∈ allFramesOrdered := by
          simp [allFramesOrdered]
          exists f.toNat
          constructor
          · exists f.toFin
          · simp
        rw [←f_eq]
        exact foldStep_mem _ f f_in_allFramesOrdered
    }

  namespace UptoIso
  end UptoIso
end FiniteKripkeFrame
