import KripkeGameAnalysis.ModalLogic.FiniteSemantics
import KripkeGameAnalysis.GenericExtras.FinsetEquivCharacteristic

import Mathlib.Data.Finset.Image

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

@[ext]
structure KripkeGameVisibleState (frameSize : ℕ) where
  accessiblityRelationSize : Fin (frameSize * frameSize + 1)
  queriesAndAnswers : List ((ModalFormula KripkeGameVars) × Fin (frameSize + 1))
deriving BEq, DecidableEq

namespace KripkeGameVisibleState

def frameSize (_ : KripkeGameVisibleState n) : ℕ := n

def InitialVisibleState (n: ℕ) : Type :=
  { state : KripkeGameVisibleState n // state.queriesAndAnswers = [] }
instance : DecidableEq (InitialVisibleState n) :=
  inferInstanceAs (DecidableEq { state : KripkeGameVisibleState n // state.queriesAndAnswers = [] })

instance : Fintype (InitialVisibleState n) :=
  let mapRelSizeToState : Fin (n * n + 1) -> InitialVisibleState n := fun accessiblityRelationSize => {
    val := { accessiblityRelationSize := accessiblityRelationSize, queriesAndAnswers := [] },
    property := by simp
  }
  let mapRelSizeToStateInj : Fin (n * n + 1) ↪ InitialVisibleState n :=
    ⟨mapRelSizeToState, by intros x y h; injections⟩

  {
    elems := Finset.univ (α := Fin (n * n + 1)).map mapRelSizeToStateInj
    complete := by
      intro x
      rw [Finset.mem_map]
      exists x.val.accessiblityRelationSize
      constructor
      -- ↑↑xval.accessiblityRelationSize ∈ Finset.univ
      · simp
      -- mapRelSizeToStateInj ↑↑xval.accessiblityRelationSize = x
      · simp only [mapRelSizeToStateInj]; simp; simp only [mapRelSizeToState]; apply Subtype.ext; simp;
        apply KripkeGameVisibleState.ext
        · simp
        · simp; exact x.property
  }

def withNewQueryAndAnswer (state : KripkeGameVisibleState n) (query : ModalFormula KripkeGameVars)
                          (answer : Fin (state.frameSize + 1)) : KripkeGameVisibleState n :=
  { state with queriesAndAnswers := (query, answer) :: state.queriesAndAnswers }

def possibleFramesUptoIso (state : KripkeGameVisibleState n) : Finset (FiniteKripkeFrame.UptoIso state.frameSize) :=
  sorry

def possibleFramesUptoIsoCard (state : KripkeGameVisibleState n) : ℕ := state.possibleFramesUptoIso.card

inductive WinningStrategy : (moves: ℕ) -> (state: KripkeGameVisibleState n) -> Type where
  | withExhaustiveSearch : possibleFramesUptoIsoCard state ≤ movesn -> WinningStrategy moves state
  | withParticularQuery : (nextQuery : ModalFormula KripkeGameVars) ->
                (Π answer : Fin (state.frameSize + 1), WinningStrategy moves (withNewQueryAndAnswer state nextQuery answer)) ->
                WinningStrategy (moves + 1) state

end KripkeGameVisibleState

def kripkeGame_winning_strategy : ∀state : KripkeGameVisibleState.InitialVisibleState 4,
                                  KripkeGameVisibleState.WinningStrategy 10 state.val :=
  sorry
