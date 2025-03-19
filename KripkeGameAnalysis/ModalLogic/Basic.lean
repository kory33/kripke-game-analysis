import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

import KripkeGameAnalysis.GenericExtras.Fin
import KripkeGameAnalysis.GenericExtras.FinsetEquivCharacteristic

inductive ModalFormula (vars : Type) : Type where
| var : vars → ModalFormula vars
| neg : ModalFormula vars → ModalFormula vars
| and : ModalFormula vars → ModalFormula vars → ModalFormula vars
| box : ModalFormula vars → ModalFormula vars
deriving BEq, DecidableEq

namespace ModalFormula
variable {vars : Type}

abbrev not := fun (φ: ModalFormula vars) => neg φ
abbrev or := fun (φ1 φ2: ModalFormula vars) => not (and (not φ1) (not φ2))
abbrev implies := fun (φ1 φ2: ModalFormula vars) => or (not φ1) φ2
abbrev dia := fun (φ: ModalFormula vars) => not (box (not φ))
end ModalFormula

/-- A Kripke frame is a directed graph.

The graph is represented by a function that takes two vertices `i` and `j` as input,
and returns `true` if there is an edge from vertex `i` to vertex `j`, and `false` otherwise.
-/
def KripkeFrame (vertices : Type) : Type := vertices → vertices → Bool
namespace KripkeFrame

instance [Fintype v] : DecidableEq (KripkeFrame v) := inferInstanceAs (DecidableEq (v → v → Bool))

@[ext] lemma ext {v : Type} {frame1 frame2 : KripkeFrame v} (h : ∀i j, frame1 i j = frame2 i j) : frame1 = frame2 :=
  funext (λ i => funext (λ j => h i j))

def vertices (_ : KripkeFrame v) : Type := v
abbrev accessible (frame : KripkeFrame v) (i j : frame.vertices) : Bool := frame i j

def Valuation (frame : KripkeFrame v) (vars : Type) : Type := vars → frame.vertices → Bool

def Valuation.decideSatisfaction {frame : KripkeFrame v} [Fintype frame.vertices]
                                  (i : frame.vertices) (fml : ModalFormula vars) (val : frame.Valuation vars) : Bool :=
match fml with
  | ModalFormula.var x => val x i
  | ModalFormula.neg φ => !(val.decideSatisfaction i φ)
  | ModalFormula.and φ1 φ2 => val.decideSatisfaction i φ1 && val.decideSatisfaction i φ2
  | ModalFormula.box φ => decide (∀j: frame.vertices, if frame.accessible i j then val.decideSatisfaction j φ else true)

section Isomorphism
@[ext] structure Isomorphism (f1 : KripkeFrame v1) (f2 : KripkeFrame v2) where
  vertex_iso : v1 ≃ v2
  preserves_accessibility : ∀i j, accessible f1 i j = accessible f2 (vertex_iso i) (vertex_iso j)

infix:50 " ≅kf " => Isomorphism

def Isomorphism.refl {v} {f : KripkeFrame v} : f ≅kf f := ⟨Equiv.refl _, by simp⟩
def Isomorphism.symm {f1 : KripkeFrame v1} {f2 : KripkeFrame v2} (iso : f1 ≅kf f2) : f2 ≅kf f1 :=
  ⟨iso.vertex_iso.symm, by simp [iso.preserves_accessibility]⟩
def Isomorphism.trans (iso1 : f1 ≅kf f2) (iso2 : f2 ≅kf f3) : f1 ≅kf f3 :=
  ⟨iso1.vertex_iso.trans iso2.vertex_iso, by simp [iso1.preserves_accessibility, iso2.preserves_accessibility]⟩

def Isomorphic (f1 : KripkeFrame v1) (f2 : KripkeFrame v2) : Prop := ∃(_ : f1 ≅kf f2), True
def Isomorphism.isomorphism (iso : f1 ≅kf f2) : Isomorphic f1 f2 := ⟨iso, trivial⟩

def isomorphism_equivalence : Equivalence (KripkeFrame.Isomorphic (v1 := v) (v2 := v)) := by
  constructor
  · intro frame; exact Isomorphism.refl.isomorphism
  · intro frame1 frame2 ⟨f, _⟩; exact f.symm.isomorphism
  · intro frame1 frame2 frame3 ⟨f1, _⟩ ⟨f2, _⟩; exact (f1.trans f2).isomorphism
end Isomorphism

instance isSetoid (v : Type) : Setoid (KripkeFrame v) :=
  ⟨KripkeFrame.Isomorphic, KripkeFrame.isomorphism_equivalence⟩

instance instFunLikeEquiv {f f' : KripkeFrame v} : FunLike (f ≅kf f') v v where
  coe iso v0 := iso.vertex_iso v0
  coe_injective' := by intro iso1 iso2 eq; ext v0; tauto

def UptoIso (v : Type) : Type := Quotient (isSetoid v)

def finNFramesEquivFinNSqPred : KripkeFrame (Fin n) ≃ (Fin (n ^ 2) → Bool) := by
  apply (Equiv.curry _ _ _).symm.trans
  refine Equiv.arrowCongr ?_ (Equiv.refl _)
  exact Fin.finPairEquivSqFin

end KripkeFrame
