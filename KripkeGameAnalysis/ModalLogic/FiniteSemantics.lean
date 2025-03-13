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
        rw [Nat.pow_two]
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
      simp only [Nat.mul_add_mod_self_right, boolFnToFrame, frameToBoolFn]; simp only [FiniteKripkeFrame, KripkeFrame] at frame
      ext i j; congr
      · calc
          (↑i * n + ↑j) / n
            = (n * ↑i + ↑j) / n := by rw [Nat.mul_comm _ _]
          _ = ↑i + ↑j / n       := by rw [Nat.mul_add_div (fin_implies_gt_zero i) i j]
          _ = ↑i                := by rw [Nat.div_eq_of_lt j.is_lt]; simp
      · exact Nat.mod_eq_of_lt j.is_lt,
    right_inv := by
      intro boolFn
      simp only [frameToBoolFn, boolFnToFrame]
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
    simp only [asKripkeFrame, Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq] at h'
    exact h'
@[simp] theorem equivToKripkeFrameFin_coe (frame : FiniteKripkeFrame n) : (equivToKripkeFrameFin frame) i j = frame i j := by rfl

abbrev mkFromKripkeFrameFin (frame : KripkeFrame (Fin n)) : FiniteKripkeFrame n := equivToKripkeFrameFin.invFun frame
@[simp] theorem mkFromKripkeFrameFin_coe (frame : KripkeFrame (Fin n)) : (mkFromKripkeFrameFin frame) i j = frame i j := by
  simp only [mkFromKripkeFrameFin, Equiv.invFun_as_coe]
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

instance KripkeFrame.finType: Fintype (KripkeFrame (Fin n)) := Fintype.ofEquiv _ FiniteKripkeFrame.equivToKripkeFrameFin

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
def FiniteValuation.equivToFinSetRepresentation {frame : FiniteKripkeFrame n}:
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
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    apply Iff.intro
    · intro iso_exists
      rcases iso_exists with ⟨iso, iso_prop⟩
      exists iso
      intros i j
      apply congrArg (· i j) at iso_prop; simp only [mkFromKripkeFrameFin_coe] at iso_prop
      simp only [KripkeFrame.accessible, Equiv.toFun_as_coe, equivToKripkeFrameFin_coe, asKripkeFrame, iso_prop]
    · intro equiv
      simp only [HasEquiv.Equiv] at equiv
      rcases equiv with ⟨iso, iso_prop⟩
      exists iso
      ext i j; simp only [mkFromKripkeFrameFin_coe]; exact (iso_prop i j).symm
abbrev enumerateClass (f : FiniteKripkeFrame n) : Finset (FiniteKripkeFrame n) := FinClassSetoid.enumerateClass f

instance : SetoidWithCanonicalizer (FiniteKripkeFrame n) where
  canonicalize f := (f.enumerateClass).min' (by
    exists f
    exact FinClassSetoid.enumerateClass_self_mem f
  )
  canonicalize_equiv_self f := by
    simp only
    set lhs := (FinClassSetoid.enumerateClass f).min' _
    apply (FinClassSetoid.enumerateClass_mem_iff lhs f).mp
    exact Finset.min'_mem _ _
  equiv_then_canonicalize_eq f f' := by
    intro h; simp only
    have enumerateClass_f_eq := (FinClassSetoid.enumerateClass_eq f f').mpr h
    simp only [enumerateClass_f_eq]
end Isomorphism

abbrev canonicalize (f : FiniteKripkeFrame n) : FiniteKripkeFrame n := SetoidWithCanonicalizer.canonicalize f
theorem canonicalize_weakly_regressive : canonicalize f ≤ f := by
  simp [canonicalize]; apply Finset.min'_le _ _; exact FinClassSetoid.enumerateClass_self_mem f
instance : DecidableEq (UptoIso n) := inferInstanceAs (DecidableEq (Quotient (isSetoid n)))

section UptoIsoFintype
private def FintypeImplLoopInvariant (seen : Std.HashSet (FiniteKripkeFrame n)) (accum : Finset (UptoIso n)) : Prop :=
  seen.toList.toFinset.image Quotient.mk' = accum
private structure FintypeImplLoopState (n : ℕ) where
  seen : Std.HashSet (FiniteKripkeFrame n)
  accum : Finset (UptoIso n)
  seen_quot_eq_accum : seen.toList.toFinset.image Quotient.mk' = accum
  seen_covering : ∀ f f', f' ∈ seen → f ≈ f' → f ∈ seen
private def FintypeImplLoopState.init : FintypeImplLoopState n :=
  {
    seen := ∅,
    accum := ∅,
    seen_quot_eq_accum := by
      simp only [Finset.image_eq_empty, List.toFinset_eq_empty_iff]
      apply List.eq_nil_of_length_eq_zero
      rw [Std.HashSet.length_toList]
      exact Std.HashSet.size_emptyc,
    seen_covering := by simp
  }
private def FintypeImplLoopState.next (frame : FiniteKripkeFrame n) (state : FintypeImplLoopState n) : FintypeImplLoopState n :=
  let ⟨seen, accum, seen_quot_eq_accum, seen_covering⟩ := state
  if h : seen.contains frame then
    state
  else
    let accum' := accum.cons (Quotient.mk' frame) (by
      rw [←seen_quot_eq_accum]
      simp
      by_contra! frame_equiv_to_some; rcases frame_equiv_to_some with ⟨x, ⟨x_in_seen, x_equiv_frame⟩⟩
      have frame_in_seen : frame ∈ seen := by
        apply seen_covering frame x x_in_seen
        simp [HasEquiv.Equiv]
        exact Setoid.iseqv.symm x_equiv_frame
      exact h frame_in_seen
    )
    let seen' := seen.insertMany (frame.enumerateClass.sort (· ≤ ·))
    {
      seen := seen',
      accum := accum',
      seen_quot_eq_accum := by
        unfold List.toFinset; rw [Finset.image_toFinset]; simp
        simp [accum']
        apply Finset.Subset.antisymm
        · intro cls cls_in_seen'_quot
          simp at cls_in_seen'_quot
          rcases cls_in_seen'_quot with ⟨frame', ⟨frame'_in_seen', frame'_eq_cls⟩⟩
          simp [seen']
          rw [← frame'_eq_cls]
          simp [seen'] at frame'_in_seen'
          rcases frame'_in_seen'
          next frame'_in_seen =>
            apply Or.inr
            rw [← seen_quot_eq_accum]; simp
            exists frame'
            apply And.intro
            · assumption
            · exact (isSetoid n).iseqv.refl _
          next frame'_in_frame_enumerateClass =>
            apply Or.inl
            apply Quotient.sound'
            apply (FinClassSetoid.enumerateClass_mem_iff frame' frame).mp
            exact frame'_in_frame_enumerateClass
        · apply Finset.insert_subset
          · simp
            exists frame
            apply And.intro
            · simp [seen']
              apply Or.inr
              exact FinClassSetoid.enumerateClass_self_mem frame
            · exact (isSetoid n).iseqv.refl _
          · rw [←seen_quot_eq_accum]
            apply Finset.image_subset_iff.mpr
            intro x h
            simp at h
            simp
            exists x; apply And.intro
            · unfold seen'
              simp
              exact Or.inl h
            · exact (isSetoid n).iseqv.refl _
        ,
      seen_covering := by
        intro f f' f'_in_seen' f_equiv_f'
        simp [seen']; simp [seen'] at f'_in_seen'
        rcases f'_in_seen'
        next f'_in_seen =>
          apply Or.inl
          exact seen_covering f f' f'_in_seen f_equiv_f'
        next f_in_frame_enumerateClass =>
          apply Or.inr
          apply (FinClassSetoid.enumerateClass_mem_iff f frame).mpr
          apply (FinClassSetoid.enumerateClass_mem_iff f' frame).mp at f_in_frame_enumerateClass
          exact (isSetoid n).iseqv.trans f_equiv_f' f_in_frame_enumerateClass
    }

instance : Fintype (UptoIso n) :=
  -- Implementation
  let allFramesOrdered : List (FiniteKripkeFrame n) := (List.finRange (2 ^ (n ^ 2))).map (BitVec.ofNat (n ^ 2))
  let elems := (allFramesOrdered.foldr FintypeImplLoopState.next FintypeImplLoopState.init).accum

  let step_elem : ∀ (frame : FiniteKripkeFrame n) state,
                  Quotient.mk' frame ∈ (FintypeImplLoopState.next frame state).accum := by
    intro frame state
    simp only [FintypeImplLoopState.next, Finset.cons_eq_insert]
    by_cases h : state.seen.contains frame
    · simp only [h, ↓reduceDIte]
      rcases state with ⟨seen, accum, seen_quot_eq_accum⟩; simp only; simp only at h
      rw [← seen_quot_eq_accum]
      apply Finset.mem_image.mpr
      exists frame; simp only [List.mem_toFinset, Std.HashSet.mem_toList, and_true]
      exact h
    · simp [h]

  let step_preserves_elem : ∀ state (frame : FiniteKripkeFrame n) frame',
                              Quotient.mk' frame ∈ state.accum →
                              Quotient.mk' frame ∈ (FintypeImplLoopState.next frame' state).accum := by
    intro state frame frame'
    simp only [FintypeImplLoopState.next, Finset.cons_eq_insert]
    by_cases h : state.seen.contains frame'
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceDIte, Finset.mem_insert]; apply Or.inr

  let step_mem : ∀ (frames : List _) frame,
                  frame ∈ frames →
                  Quotient.mk' frame ∈ (frames.foldr FintypeImplLoopState.next FintypeImplLoopState.init).accum := by
    intro frames
    induction frames with
    | nil => simp
    | cons head_frame frames ih =>
      intro frame hyp
      cases hyp
      next => exact step_elem _ _
      next frame_in_frames => simp only [List.foldr_cons]; exact step_preserves_elem _ _ _ (ih _ frame_in_frames)
  {
    elems := elems,
    complete := by
      intro fUptoIso
      rcases Quotient.exists_rep fUptoIso with ⟨f, f_eq⟩
      rw [←f_eq]
      have f_in_allFramesOrdered : f ∈ allFramesOrdered := by
        simp only [List.mem_map, allFramesOrdered]
        exists f.toNat
        constructor
        · simp only [List.bind_eq_flatMap, List.mem_flatMap]
          exists f.toFin
          simp
        · simp
      exact step_mem _ f f_in_allFramesOrdered
  }

end UptoIsoFintype
end FiniteKripkeFrame
