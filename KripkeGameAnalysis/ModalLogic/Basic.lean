import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

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
  def vertices (_ : KripkeFrame v) : Type := v
  def accessible (frame : KripkeFrame v) (i j : frame.vertices) : Bool := frame i j

  def Valuation (frame : KripkeFrame v) (vars : Type) : Type := vars → frame.vertices → Bool

  def Valuation.decideSatisfaction {frame : KripkeFrame v} [Fintype frame.vertices]
                                   (i : frame.vertices) (fml : ModalFormula vars) (val : frame.Valuation vars) : Bool :=
  match fml with
    | ModalFormula.var x => val x i
    | ModalFormula.neg φ => !(val.decideSatisfaction i φ)
    | ModalFormula.and φ1 φ2 => val.decideSatisfaction i φ1 && val.decideSatisfaction i φ2
    | ModalFormula.box φ => decide (∀j: frame.vertices, if frame.accessible i j then val.decideSatisfaction j φ else true)

end KripkeFrame
