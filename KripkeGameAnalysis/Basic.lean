import KripkeGameAnalysis.ModalLogic.Basic
import KripkeGameAnalysis.GenericExtras.Fintype

inductive KripkeGameVars : Type
| p
| q
| r
| s
deriving Ord, BEq, DecidableEq

instance KripkeGameVars.fintype : Fintype KripkeGameVars :=
  open KripkeGameVars in ⟨⟨{p, q, r, s}, by simp⟩, fun x => by cases x <;> simp⟩

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
  -- An initial visible state should have a frame size of 4, and an empty query-answer list.
  def InitialVisibleState : Type :=
   { state : KripkeGameVisibleState // state.frameSize = 4 ∧ state.queriesAndAnswers = [] }

  instance : Fintype InitialVisibleState := sorry

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

def kripkeGame_winning_strategy : ∀state : KripkeGameVisibleState.InitialVisibleState,
                                  KripkeGameVisibleState.WinningStrategy 10 state.val :=
  sorry
