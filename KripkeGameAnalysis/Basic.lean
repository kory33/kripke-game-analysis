import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

import KripkeGameAnalysis.GenericExtras.FinsetEquivCharacteristic

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

inductive ModalFormula (vars : Type) : Type where
| var : vars → ModalFormula vars
| neg : ModalFormula vars → ModalFormula vars
| and : ModalFormula vars → ModalFormula vars → ModalFormula vars
| box : ModalFormula vars → ModalFormula vars

namespace ModalFormula
  abbrev p := var KripkeGameVars.p
  abbrev q := var KripkeGameVars.q
  abbrev r := var KripkeGameVars.r
  abbrev s := var KripkeGameVars.s

  variable {finVars : Type} [Fintype finVars] [DecidableEq finVars]

  abbrev not := fun (φ: ModalFormula finVars) => neg φ
  abbrev or := fun (φ1 φ2: ModalFormula finVars) => not (and (not φ1) (not φ2))
  abbrev implies := fun (φ1 φ2: ModalFormula finVars) => or (not φ1) φ2
  abbrev dia := fun (φ: ModalFormula finVars) => not (box (not φ))
end ModalFormula

/-- A Kripke frame of `frameSize` possible worlds is a directed graph with `frameSize` nodes.

We think of the nodes in the graph as being numbered from `0` to `frameSize - 1`, inclusive,
and we think the `j`-th node is accessible from the `i`-th node if and only if there is an edge from `i` to `j`.

The graph, then, is represented by a function that takes two natural numbers `n` and `m` as input,
and returns `true` if there is an edge from node `n` to node `m`, and `false` otherwise.
-/
def KripkeFrame (frameSize : Nat) : Type := Fin frameSize → Fin frameSize → Bool
namespace KripkeFrame
  def Node (_ : KripkeFrame frameSize) := Fin frameSize
  instance (frame : KripkeFrame n) : Fintype frame.Node := inferInstanceAs (Fintype (Fin n))
  instance (frame : KripkeFrame n) : DecidableEq frame.Node := inferInstanceAs (DecidableEq (Fin n))

  def allNodes (frame : KripkeFrame n) : Finset frame.Node := Finset.univ
  lemma allNodes_card_eq_frameSize (frame : KripkeFrame n) : frame.allNodes.card = n :=
    by apply Fintype.card_fin

  def accessible (frame : KripkeFrame n) (i j : frame.Node) : Bool := frame i j
  def accessibilityRelationCount (frame : KripkeFrame n) : ℕ :=
    ((frame.allNodes.product (frame.allNodes)).filter (fun a => frame.accessible a.fst a.snd)).card

  def Valuation (frame : KripkeFrame n) (vars : Type) : Type := vars → frame.Node → Bool

  def Valuation.satisfiesAt {frame : KripkeFrame n} (i : frame.Node) (fml : ModalFormula vars) (val : frame.Valuation vars) : Bool :=
  match fml with
    | ModalFormula.var x => val x i
    | ModalFormula.neg φ => !(val.satisfiesAt i φ)
    | ModalFormula.and φ1 φ2 => val.satisfiesAt i φ1 && val.satisfiesAt i φ2
    | ModalFormula.box φ => decide (∀j ∈ frame.allNodes, if frame.accessible i j then val.satisfiesAt j φ else true)

  def Valuation.isoToFinSetEquiv {frame : KripkeFrame n}: (Finset (KripkeGameVars × frame.Node)) ≃ (frame.Valuation KripkeGameVars) :=
    finsetProdEquivCurriedCharacteristic

  def allValuations (frame : KripkeFrame n) : Finset (frame.Valuation KripkeGameVars) :=
    let valuationsAsPsets := (Finset.product KripkeGameVars.all frame.allNodes).powerset
    valuationsAsPsets.map ((@KripkeFrame.Valuation.isoToFinSetEquiv _ frame).toEmbedding)

  def Node.satisfiesForAllValuations {frame : KripkeFrame n} (i : frame.Node) (fml : ModalFormula KripkeGameVars) : Bool :=
    decide (∀val ∈ frame.allValuations, val.satisfiesAt i fml)

  def countSatisfyingNodes (frame : KripkeFrame n) (fml : ModalFormula KripkeGameVars) : ℕ :=
    (frame.allNodes.filter (fun i => i.satisfiesForAllValuations fml)).card

  lemma countSatisfyingNodes_leq_frameSize
    (frame : KripkeFrame n) (fml : ModalFormula KripkeGameVars) : frame.countSatisfyingNodes fml ≤ n := by
    simp only [KripkeFrame.countSatisfyingNodes]
    simp only [← frame.allNodes_card_eq_frameSize]
    apply Finset.card_filter_le
end KripkeFrame

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

  def possibleFramesUptoIso (state : KripkeGameVisibleState) : Finset (KripkeFrame state.frameSize) :=
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
