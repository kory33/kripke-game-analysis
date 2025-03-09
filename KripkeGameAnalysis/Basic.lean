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

namespace ModalFormula
  variable {vars : Type}

  abbrev not := fun (φ: ModalFormula vars) => neg φ
  abbrev or := fun (φ1 φ2: ModalFormula vars) => not (and (not φ1) (not φ2))
  abbrev implies := fun (φ1 φ2: ModalFormula vars) => or (not φ1) φ2
  abbrev dia := fun (φ: ModalFormula vars) => not (box (not φ))
end ModalFormula

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

/-- A Kripke frame of `frameSize` possible worlds is a directed graph with `frameSize` vertices.

We think of the vertices in the graph as being numbered from `0` to `frameSize - 1`, inclusive,
and we think the `j`-th vertex is accessible from the `i`-th vertex if and only if there is an edge from `i` to `j`.

The graph, then, is represented by a function that takes two natural numbers `n` and `m` as input,
and returns `true` if there is an edge from vertex `n` to vertex `m`, and `false` otherwise.
-/
def FiniteKripkeFrame (frameSize : Nat) : Type := KripkeFrame (Fin frameSize)
namespace FiniteKripkeFrame
  instance (frame : FiniteKripkeFrame n) : Fintype frame.vertices := inferInstanceAs (Fintype (Fin n))
  instance (frame : FiniteKripkeFrame n) : DecidableEq frame.vertices := inferInstanceAs (DecidableEq (Fin n))

  def allNodes (frame : FiniteKripkeFrame n) : Finset frame.vertices := Finset.univ
  lemma allNodes_card_eq_frameSize (frame : FiniteKripkeFrame n) : frame.allNodes.card = n :=
    by apply Fintype.card_fin

  def accessibilityRelationCount (frame : FiniteKripkeFrame n) : ℕ :=
    ((frame.allNodes.product (frame.allNodes)).filter (fun a => frame.accessible a.fst a.snd)).card

  structure FiniteValuation (frame : FiniteKripkeFrame n) (vars : Type) [Fintype vars] [DecidableEq vars] where
    valuation : frame.Valuation vars

  namespace FiniteValuation
    def equivToFinSetRepresentation {finVars : Type} {frame : FiniteKripkeFrame n} [Fintype finVars] [DecidableEq finVars]:
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

  def allValuations (frame : FiniteKripkeFrame n) (finVars : Type) [varsFin : Fintype finVars] [DecidableEq finVars] : Finset (frame.FiniteValuation finVars) :=
    let valuationsAsPsets := (Finset.product varsFin.elems frame.allNodes).powerset
    valuationsAsPsets.map ((@FiniteValuation.equivToFinSetRepresentation _ _ frame).symm.toEmbedding)

  def satisfiesForAllValuations {frame : FiniteKripkeFrame n} (finVars : Type) [Fintype finVars] [DecidableEq finVars]
                                (i : frame.vertices) (fml : ModalFormula finVars) : Bool :=
    decide (∀finval ∈ frame.allValuations finVars, finval.valuation.decideSatisfaction i fml)

  def countSatisfyingNodes (frame : FiniteKripkeFrame n)
                           (fml : ModalFormula finVars) [Fintype finVars] [DecidableEq finVars] : ℕ :=
    (frame.allNodes.filter (fun i => satisfiesForAllValuations finVars i fml)).card

  lemma countSatisfyingNodes_leq_frameSize
    (frame : FiniteKripkeFrame n) (fml : ModalFormula finVars)
    [Fintype finVars] [DecidableEq finVars]: frame.countSatisfyingNodes fml ≤ n := by
    simp only [FiniteKripkeFrame.countSatisfyingNodes]
    simp only [← frame.allNodes_card_eq_frameSize]
    apply Finset.card_filter_le
end FiniteKripkeFrame

inductive KripkeGameVars : Type
| p
| q
| r
| s
deriving Ord, BEq, DecidableEq

instance KripkeGameVars.fintype : Fintype KripkeGameVars :=
  open KripkeGameVars in
  ⟨⟨{p, q, r, s}, by simp⟩, fun x => by cases x <;> simp⟩

def KripkeGameVars.all : Finset KripkeGameVars := Finset.univ

namespace ModalFormula
  abbrev p := var KripkeGameVars.p
  abbrev q := var KripkeGameVars.q
  abbrev r := var KripkeGameVars.r
  abbrev s := var KripkeGameVars.s
end ModalFormula

structure KripkeGameVisibleState where
  frameSize : ℕ
  accessiblityRelationSize : Fin (frameSize * frameSize + 1)
  queriesAndAnswers : List ((ModalFormula KripkeGameVars) × Fin (frameSize + 1))

namespace KripkeGameVisibleState
  def allPossibleInitialVisibleStates : Finset KripkeGameVisibleState :=
    let frameSize := 4
    let maxRelSize := frameSize * frameSize
    let mapRelSizeToState := fun (n : Fin (maxRelSize + 1)) =>
      {
        frameSize := frameSize,
        accessiblityRelationSize := n,
        queriesAndAnswers := []
        : KripkeGameVisibleState
      }
    let mappingInjective: Function.Injective mapRelSizeToState := by
      intro n1 n2 h; simp only [mapRelSizeToState] at h; injection h
    (Finset.univ : Finset (Fin (4 * 4 + 1))).map ⟨mapRelSizeToState, mappingInjective⟩

  def withNewQueryAndAnswer (state : KripkeGameVisibleState) (query : ModalFormula KripkeGameVars) (answer : Fin (state.frameSize + 1)) : KripkeGameVisibleState :=
    { state with queriesAndAnswers := (query, answer) :: state.queriesAndAnswers }

  def possibleFramesUptoIso (state : KripkeGameVisibleState) : Finset (FiniteKripkeFrame state.frameSize) :=
    sorry

  def possibleFramesUptoIsoCard (state : KripkeGameVisibleState) : ℕ := state.possibleFramesUptoIso.card

  inductive WinningStrategy : (n: ℕ) -> (state: KripkeGameVisibleState) -> Type where
    | withExhaustiveSearch : possibleFramesUptoIsoCard state ≤ n -> WinningStrategy n state
    | withParticularQuery : (nextQuery : ModalFormula KripkeGameVars) ->
                  (Π answer : Fin (state.frameSize + 1), WinningStrategy n (state.withNewQueryAndAnswer nextQuery answer)) ->
                  WinningStrategy (n + 1) state
end KripkeGameVisibleState

def kripkeGame_winning_strategy : ∀state ∈ KripkeGameVisibleState.allPossibleInitialVisibleStates,
                                  KripkeGameVisibleState.WinningStrategy 10 state :=
  sorry
