import Init.Data.BitVec.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Insert

import KripkeGameAnalysis.Generic.FinClassSetoid
import KripkeGameAnalysis.Generic.SetoidWithCanonicalizer
import KripkeGameAnalysis.GenericExtras.Array
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

def ofFin (i : Fin (2 ^ (n ^ 2))) : FiniteKripkeFrame n := BitVec.ofFin i
def asBitVec (frame : FiniteKripkeFrame n) : BitVec (n ^ 2) := frame

@[simp] lemma ofFin_asBitVec_toFin_eq : ofFin (asBitVec f).toFin = f := by cases f; simp [ofFin, asBitVec]
@[simp] lemma ofFin_fin_asBitVec_toFin_eq : (ofFin i).asBitVec.toFin = i := by simp only [ofFin, asBitVec]

def equivToKripkeFrameFin: FiniteKripkeFrame n ≃ KripkeFrame (Fin n) := by
  apply (BitVec.equivToBitPred (n ^ 2)).trans
  exact KripkeFrame.finNFramesEquivFinNSqPred.symm

instance instLinOrd : LinearOrder (FiniteKripkeFrame n) where
  le := fun f1 f2 => (f1 : BitVec (n ^ 2)).ule f2
  le_refl := by intro f; simp [BitVec.ule]
  le_trans := by intro f1 f2 f3; simp [BitVec.ule]; exact Nat.le_trans
  le_antisymm := by intro f1 f2; simp [BitVec.ule]; intro h1 h2; apply BitVec.eq_of_toNat_eq; apply Nat.le_antisymm h1 h2
  le_total := by intro f1 f2; simp [BitVec.ule]; exact Nat.le_total _ _
  toDecidableLE := fun f1 f2 => inferInstanceAs (Decidable ((f1 : BitVec (n ^ 2)).ule f2))
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

lemma getElem_eq_apply_finPairEquivSqFin_pair {frame : FiniteKripkeFrame n} (ij : Fin (n ^ 2)) :
  Function.uncurry frame (Fin.finPairEquivSqFin.symm ij) = frame.asBitVec[ij] := by
  suffices pred_eq : ∀ p, p ij =
                        (KripkeFrame.finNFramesEquivFinNSqPred.symm) p
                          (Fin.finPairEquivSqFin.symm ij).1
                          (Fin.finPairEquivSqFin.symm ij).2 by
    apply Eq.symm
    rw [Function.uncurry, DFunLike.coe]
    dsimp only [instFunLike, asKripkeFrame, equivToKripkeFrameFin]
    simp only [Equiv.trans, Function.comp, ←pred_eq, BitVec.equivToBitPred, Equiv.coe_fn_mk, asBitVec]
  intro pred
  simp only [KripkeFrame.finNFramesEquivFinNSqPred, Equiv.trans, Equiv.symm, Equiv.coe_fn_mk]
  simp [Equiv.curry, Function.comp]

lemma getElem_finPairEquivSqFin_equivalence_eq_apply_apply {frame : FiniteKripkeFrame n} (i j : Fin n) :
  frame.asBitVec[Fin.finPairEquivSqFin.toFun (i, j)] = frame i j := by
  rw [←getElem_eq_apply_finPairEquivSqFin_pair]; simp

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

end FiniteKripkeFrame

instance KripkeFrame.finType: Fintype (KripkeFrame (Fin n)) := Fintype.ofEquiv _ FiniteKripkeFrame.equivToKripkeFrameFin

namespace FiniteKripkeFrame

def allNodes (frame : FiniteKripkeFrame n) : Finset frame.vertices := Finset.univ
lemma allNodes_card_eq_frameSize (frame : FiniteKripkeFrame n) : frame.allNodes.card = n :=
  by apply Fintype.card_fin

def accessibilityRelationCount (frame : FiniteKripkeFrame n) : ℕ :=
  let asBitVec : BitVec (n ^ 2) := frame
  (Finset.univ.filter (fun (i : Fin (n ^ 2)) => asBitVec[i])).card

def accessibilityRelationCount_eq_card_of_accessible_pairs (frame : FiniteKripkeFrame n) :
    frame.accessibilityRelationCount = (Finset.univ.filter fun (i, j) => frame i j).card := by
  dsimp only [accessibilityRelationCount]
  refine (Finset.card_equiv Fin.finPairEquivSqFin ?_).symm
  intro ⟨i, j⟩
  have := getElem_finPairEquivSqFin_equivalence_eq_apply_apply (frame := frame) i j
  simpa [this]

section FiniteValuation
abbrev FiniteValuation (frame : FiniteKripkeFrame n) (finVars : Type) [Fintype finVars] [DecidableEq finVars] :=
  frame.asKripkeFrame.Valuation finVars

abbrev FiniteValuation.reinterpretAsValuationFor [Fintype vars] [DecidableEq vars] {f1 : FiniteKripkeFrame n}
                                                 (val : f1.FiniteValuation vars)
                                                 (f2 : FiniteKripkeFrame n) : f2.FiniteValuation vars := val

variable {finVars : Type} [Fintype finVars] [DecidableEq finVars]
def FiniteValuation.equivToFinSetRepresentation {frame : FiniteKripkeFrame n}:
                                (frame.FiniteValuation finVars) ≃ (Finset (finVars × frame.vertices)) :=
  finsetProdEquivCurriedCharacteristic.symm

def allFinValuations (frame : FiniteKripkeFrame n) : Finset (frame.FiniteValuation finVars) :=
  let valuationsAsPsets := (Finset.product (inferInstance (α := Fintype finVars)).elems frame.allNodes).powerset
  valuationsAsPsets.map (FiniteValuation.equivToFinSetRepresentation (frame := frame).symm.toEmbedding)

def allFinValuations_mem (frame : FiniteKripkeFrame n)
                         (val : frame.FiniteValuation finVars) : val ∈ frame.allFinValuations := by
  suffices _ : Finset.filter (fun a => val a.1 a.2 = true) Finset.univ ⊆ Finset.univ ×ˢ Finset.univ by
    simp only [
      allFinValuations,
      Finset.product_eq_sprod, Finset.mem_map_equiv, Finset.mem_powerset,
      Equiv.symm_symm
    ]
    simpa only
  simp only [Finset.univ_product_univ, Finset.subset_univ]

def satisfiesForAllValuations (frame : FiniteKripkeFrame n) (i : frame.vertices) (fml : ModalFormula finVars) : Bool :=
  decide (∀finval ∈ frame.allFinValuations, finval.decideSatisfaction i fml)

def countSatisfyingNodes (frame : FiniteKripkeFrame n) (fml : ModalFormula finVars) : ℕ :=
  (frame.allNodes.filter (fun i => satisfiesForAllValuations frame i fml)).card

lemma countSatisfyingNodes_leq_frameSize: ∀ {frame : FiniteKripkeFrame n} {fml : ModalFormula finVars},
                                            frame.countSatisfyingNodes fml ≤ n := by
  intro frame fml
  dsimp only [FiniteKripkeFrame.countSatisfyingNodes]
  simp only [← frame.allNodes_card_eq_frameSize]
  apply Finset.card_filter_le

end FiniteValuation

section Isomorphism

def Isomorphism (f1 : FiniteKripkeFrame n) (f2 : FiniteKripkeFrame n) : Type :=
  f1.asKripkeFrame ≅kf f2.asKripkeFrame
infix:50 " ≅kf " => Isomorphism

instance isSetoid (n : ℕ) : Setoid (FiniteKripkeFrame n) where
  r := fun frame1 frame2 => frame1.asKripkeFrame ≈ frame2
  iseqv := by
    constructor
    · intro _; exact Setoid.refl _
    · intro _ _ h; exact Setoid.symm h
    · intro _ _ _ h1 h2; exact Setoid.trans h1 h2
lemma kfIso_implies_equiv {f1 f2 : FiniteKripkeFrame n} (iso : f1 ≅kf f2) : (f1 ≈ f2) := by tauto
instance instFunLikeEquiv {f f' : FiniteKripkeFrame n} : FunLike (f ≅kf f') (Fin n) (Fin n) :=
  inferInstanceAs (FunLike (f.asKripkeFrame ≅kf f'.asKripkeFrame) (Fin n) (Fin n))


def UptoIso (n: ℕ) : Type := Quotient (isSetoid n)

instance FinClassSetoid (n : ℕ) : FinClassSetoid (FiniteKripkeFrame n) where
  enumerateClass := fun f =>
    let permutateFrame : Equiv.Perm (Fin n) → FiniteKripkeFrame n := fun f' =>
      mkFromKripkeFrameFin (fun i j => f (f' i) (f' j))
    Finset.univ (α := Equiv.Perm (Fin n)).image permutateFrame
  enumerateClass_mem_iff f f' := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    apply Iff.intro
    · intro perm_exists
      rcases perm_exists with ⟨perm, perm_prop⟩
      exact kfIso_implies_equiv {
        vertex_iso := perm,
        preserves_accessibility := by intro i j; rw [←perm_prop]; simp [asKripkeFrame]
      }
    · intro equiv; dsimp only [HasEquiv.Equiv] at equiv
      rcases equiv with ⟨perm, perm_prop⟩
      exists perm
      ext i j; simp only [mkFromKripkeFrameFin_coe]
      exact (perm_prop i j).symm
abbrev enumerateClass (f : FiniteKripkeFrame n) : Finset (FiniteKripkeFrame n) := FinClassSetoid.enumerateClass f

instance : SetoidWithCanonicalizer (FiniteKripkeFrame n) where
  canonicalize f := (f.enumerateClass).min' (by
    exists f
    exact FinClassSetoid.enumerateClass_self_mem f
  )
  canonicalize_equiv_self f := by
    set lhs := (FinClassSetoid.enumerateClass f).min' _
    apply (FinClassSetoid.enumerateClass_mem_iff lhs f).mp
    exact Finset.min'_mem _ _
  equiv_then_canonicalize_eq f f' := by
    intro h
    have enumerateClass_f_eq := (FinClassSetoid.enumerateClass_eq f f').mpr h
    simp only [enumerateClass_f_eq]
end Isomorphism

abbrev canonicalize (f : FiniteKripkeFrame n) : FiniteKripkeFrame n := SetoidWithCanonicalizer.canonicalize f
theorem canonicalize_weakly_regressive : canonicalize f ≤ f := by
  simp [canonicalize]; apply Finset.min'_le _ _; exact FinClassSetoid.enumerateClass_self_mem f
instance : DecidableEq (UptoIso n) := inferInstanceAs (DecidableEq (Quotient (isSetoid n)))

namespace UptoIso
private structure FintypeImplLoopState (n : ℕ) where
  /-- isomorphic to Finset (FiniteKripkeFrame n), since
        FiniteKripkeFrame n
         ≅ KripkeFrame (Fin n)
         ≅ Fin n → Fin n → Bool
         ≅ Fin (n * n) → Bool
         ≅ Fin (2 ^ (n * n))
      and Finset (Fin (2 ^ (n * n))) ≅ BitVec (2 ^ (n * n)) ≅ Array Bool (with size 2 ^ (n * n))
    -/
  seen : Array Bool
  accum : Finset (UptoIso n)
  -- invariants
  seen_size : seen.size = 2 ^ (n ^ 2)
  seen_eq_quot_in_accum : ∀ (i : Fin (2 ^ (n ^ 2))), seen[i] = (⟦ofFin i⟧ ∈ accum)
  seen_covering : ∀ (f f' : FiniteKripkeFrame n), f ≈ f' → seen[f'.asBitVec.toFin] = seen[f.asBitVec.toFin]

private def FintypeImplLoopState.init : FintypeImplLoopState n :=
  {
    seen := Array.replicate (2 ^ (n ^ 2)) false,
    accum := ∅,
    seen_size := by simp,
    seen_eq_quot_in_accum := by simp,
    seen_covering := by simp
  }
private def FintypeImplLoopState.next (frame : FiniteKripkeFrame n) (state : FintypeImplLoopState n) : FintypeImplLoopState n :=
  let ⟨seen, accum, seen_size, seen_eq_quot_in_accum, seen_covering⟩ := state
  if h : seen[frame.asBitVec.toFin] then
    state
  else
    let accum' := accum.cons ⟦frame⟧ (by
      have := seen_eq_quot_in_accum frame.asBitVec.toFin
      simp only [ofFin_asBitVec_toFin_eq] at this
      simp only [← this, h, Bool.false_eq_true, not_false_eq_true]
    )
    let setTrueOnSeenAt := fun f : FiniteKripkeFrame n => seen.set f.asBitVec.toFin true
    let equivClassAsFin := frame.enumerateClass.map ⟨(·.asBitVec.toFin), by
      intro f f' h; simp only [asBitVec] at h;
      cases f; cases f'; simp only at h; simp only [h]
    ⟩
    have equivClassAsFin_mem : ∀ i, i ∈ equivClassAsFin ↔ (@Eq (UptoIso n) ⟦ofFin i⟧ ⟦frame⟧) := by
      intro i; unfold equivClassAsFin
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, FinClassSetoid.enumerateClass_mem_iff]
      apply Iff.intro
      · intro ⟨f, ⟨f_iso_frame, f_eq_i⟩⟩
        rw [←f_eq_i, ofFin_asBitVec_toFin_eq]
        exact Quotient.sound f_iso_frame
      · intro h
        exists (ofFin i)
        exact ⟨Quotient.eq_iff_equiv.mp h, ofFin_fin_asBitVec_toFin_eq⟩
    let seen' := seen.setValueAtIndices seen_size equivClassAsFin true
    {
      seen := seen',
      accum := accum',
      seen_size := by unfold seen'; rw [Array.setValueAtIndices_size, seen_size]
      seen_eq_quot_in_accum := by
        unfold seen'; unfold accum'
        intro i
        rw [Array.setValueAtIndices_eq]
        suffices _ : i ∈ equivClassAsFin ∨ seen[i] = true ↔ ⟦ofFin i⟧ = ⟦frame⟧ ∨ ⟦ofFin i⟧ ∈ accum by
          simpa only [Bool.if_true_left, Bool.or_eq_true, decide_eq_true_eq, Finset.cons_eq_insert, Finset.mem_insert, eq_iff_iff]
        rw [seen_eq_quot_in_accum i, equivClassAsFin_mem]
      seen_covering := by
        intro f f' f_equiv_f'
        unfold seen' at *
        rw [Array.setValueAtIndices_eq, Array.setValueAtIndices_eq]
        have equivClassAsFin_eq : decide (f.asBitVec.toFin ∈ equivClassAsFin) = decide (f'.asBitVec.toFin ∈ equivClassAsFin) := by
          simp only [decide_eq_decide]
          rw [
            equivClassAsFin_mem, equivClassAsFin_mem,
            ofFin_asBitVec_toFin_eq, ofFin_asBitVec_toFin_eq,
            Quotient.eq_iff_equiv.mpr f_equiv_f'
          ]
        simp [equivClassAsFin_eq, seen_covering f f' f_equiv_f']
    }

instance : Fintype (UptoIso n) :=
  -- Implementation
  let allFramesOrdered : List (FiniteKripkeFrame n) := (List.finRange (2 ^ (n ^ 2))).map (BitVec.ofNat (n ^ 2))
  let elems := (allFramesOrdered.foldr FintypeImplLoopState.next FintypeImplLoopState.init).accum

  have step_elem : ∀ (frame : FiniteKripkeFrame n) state,
                  ⟦frame⟧ ∈ (FintypeImplLoopState.next frame state).accum := by
    intro frame state
    simp only [FintypeImplLoopState.next, Finset.cons_eq_insert]
    by_cases h : state.seen[frame.asBitVec.toFin]'(by rw [state.seen_size]; exact frame.toFin.is_lt) = true
    · suffices _ : ⟦frame⟧ ∈ state.accum by simpa [h]
      rw [←ofFin_asBitVec_toFin_eq (f := frame), ←state.seen_eq_quot_in_accum (frame.asBitVec.toFin), h]
    · simp [h]

  have step_preserves_elem : ∀ state (frame : FiniteKripkeFrame n) frame',
                              ⟦frame⟧ ∈ state.accum →
                              ⟦frame⟧ ∈ (FintypeImplLoopState.next frame' state).accum := by
    intro state frame frame'
    simp only [FintypeImplLoopState.next, Finset.cons_eq_insert]
    by_cases h : state.seen[frame'.asBitVec.toFin]'(by rw [state.seen_size]; exact frame'.toFin.is_lt) = true
    · simp [h]
    · simp only [h, Bool.false_eq_true, ↓reduceDIte, Finset.mem_insert]; apply Or.inr

  have step_mem : ∀ (frames : List _) frame,
                  frame ∈ frames →
                  ⟦frame⟧ ∈ (frames.foldr FintypeImplLoopState.next FintypeImplLoopState.init).accum := by
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
abbrev univ (n : ℕ) : Finset (UptoIso n) := Finset.univ

def accessibilityRelationCount (f : UptoIso n) : ℕ := f.liftOn (·.accessibilityRelationCount) (by
  intro f1 f2 h; rcases h with ⟨iso, iso_prop⟩; dsimp only
  rw [
    accessibilityRelationCount_eq_card_of_accessible_pairs,
    accessibilityRelationCount_eq_card_of_accessible_pairs
  ]; dsimp only
  let pair_iso : (Fin n × Fin n) ≃ (Fin n × Fin n) := {
    toFun := fun (i, j) => (iso i, iso j),
    invFun := fun (i, j) => (iso.invFun i, iso.invFun j),
    left_inv := by simp [Function.LeftInverse]
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }
  refine Finset.card_equiv pair_iso ?_
  · suffices _ : ∀ (a b : Fin n), f1 a b = f2 (iso a) (iso b) by simpa
    intro a b; simpa [KripkeFrame.accessible] using (iso_prop a b)
)

lemma satisfiesForAllValuations_iso_eq [Fintype finVars] [DecidableEq finVars]
                                       {f1 f2 : FiniteKripkeFrame n} {i : Fin n} {fml : ModalFormula finVars}
                                       (iso : f1 ≅kf f2) :
  f2.satisfiesForAllValuations (iso i) fml = f1.satisfiesForAllValuations i fml := by
  simp only [satisfiesForAllValuations, decide_eq_decide, allFinValuations_mem, forall_const]
  apply Iff.intro
  · intro h f1Val
    rw [←KripkeFrame.Valuation.decideSatisfaction_iso iso f1Val]
    simp [h]
  · intro h f2Val
    rw [←KripkeFrame.Valuation.decideSatisfaction_iso iso.symm f2Val, KripkeFrame.iso_symm_iso]
    simp [h]

def countSatisfyingNodes [Fintype finVars] [DecidableEq finVars]
                         (f : UptoIso n) (fml : ModalFormula finVars) : ℕ := f.liftOn (·.countSatisfyingNodes fml) (by
  intro f1 f2 h
  dsimp only [FiniteKripkeFrame.countSatisfyingNodes]
  have iso := Classical.choice h
  refine Finset.card_equiv iso.vertex_iso ?_
  intro i
  suffices _ : satisfiesForAllValuations f1 i fml = satisfiesForAllValuations f2 (iso i) fml by simpa [allNodes]
  rw [satisfiesForAllValuations_iso_eq iso]
)

end UptoIso
end FiniteKripkeFrame
