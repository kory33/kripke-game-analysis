import KripkeGameAnalysis.Game.Basic
import KripkeGameAnalysis.ModalLogic.FiniteSemantics

inductive KripkeGameWinningStrategy : (moves: ℕ) -> (state: KripkeGameVisibleState n) -> Type where
  | withExhaustiveSearch : KripkeGameVisibleState.possibleFramesUptoIsoCard state ≤ moves -> KripkeGameWinningStrategy moves state
  | withParticularQuery : (nextQuery : ModalFormula KripkeGameVars) ->
                (Π answer : Fin (state.frameSize + 1), KripkeGameWinningStrategy moves (KripkeGameVisibleState.withNewQueryAndAnswer state nextQuery answer)) ->
                KripkeGameWinningStrategy (moves + 1) state

inductive KripkeGameStrategy (frameSize : ℕ) : Type where
  | proceedWithExhaustiveSearch : KripkeGameStrategy frameSize
  | askQueryAndThen :
      (query : ModalFormula KripkeGameVars) ->
      (continuations : Fin (frameSize + 1) -> KripkeGameStrategy frameSize) ->
      KripkeGameStrategy frameSize
deriving Inhabited

namespace KripkeGameStrategy

variable {n : ℕ}

def allFin {n : ℕ} (f : Fin n -> Bool) : Bool :=
  (List.finRange n).all f

theorem allFin_true_then_true {n : ℕ} {f : Fin n -> Bool} (h : allFin f = true) : ∀ i : Fin n, f i = true := by
  intro i
  unfold allFin at h
  apply List.all_eq_true.mp h i
  exact List.mem_finRange i

def is_winning_strategy (strategy : KripkeGameStrategy n) (moves : ℕ) (state : KripkeGameVisibleState n) : Bool :=
  match strategy, moves with
  | proceedWithExhaustiveSearch, moves =>
      decide (state.possibleFramesUptoIsoCard ≤ moves)
  | askQueryAndThen _ _, 0 =>
      false  -- Can't ask a query with no moves remaining
  | askQueryAndThen query continuations, moves + 1 =>
      -- Check that all possible answers lead to winning strategies
      allFin (fun answer =>
        is_winning_strategy
          (continuations answer)
          moves
          (state.withNewQueryAndAnswer query answer))

def as_winning_strategy (strategy : KripkeGameStrategy n) (moves : ℕ) (state : KripkeGameVisibleState n)
                        (h : is_winning_strategy strategy moves state = true) :
                        KripkeGameWinningStrategy moves state :=
  match strategy, moves with
  | proceedWithExhaustiveSearch, moves =>
      KripkeGameWinningStrategy.withExhaustiveSearch (by
        unfold is_winning_strategy at h
        exact of_decide_eq_true h
      )
  | askQueryAndThen query continuations, moves + 1 =>
      KripkeGameWinningStrategy.withParticularQuery query (fun answer =>
        as_winning_strategy
          (continuations answer)
          moves
          (state.withNewQueryAndAnswer query answer)
          (by
            unfold is_winning_strategy at h
            exact allFin_true_then_true h answer
          )
      )

end KripkeGameStrategy
