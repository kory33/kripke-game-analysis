import KripkeGameAnalysis.Game.Basic
import KripkeGameAnalysis.ModalLogic.FiniteSemantics

inductive KripkeGameWinningStrategy : (moves: ℕ) -> (state: KripkeGameVisibleState n) -> Type where
  | withExhaustiveSearch : KripkeGameVisibleState.possibleFramesUptoIsoCard state ≤ moves -> KripkeGameWinningStrategy moves state
  | withParticularQuery : (nextQuery : ModalFormula KripkeGameVars) ->
                (Π answer : Fin (state.frameSize + 1), KripkeGameWinningStrategy moves (KripkeGameVisibleState.withNewQueryAndAnswer state nextQuery answer)) ->
                KripkeGameWinningStrategy (moves + 1) state

inductive KripkeGamePartialStrategy (frameSize : ℕ) : Type where
  | proceedWithExhaustiveSearch : KripkeGamePartialStrategy frameSize
  | askQueryAndThen :
      (query : ModalFormula KripkeGameVars) ->
      -- expectation is that continuations.size = frameSize + 1, but
      -- we can enforce that constraint at is_winning_strategy time
      (continuations : Array (KripkeGamePartialStrategy frameSize)) ->
      KripkeGamePartialStrategy frameSize
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

theorem allFin_ext {n : ℕ} {f g : Fin n -> Bool} (h : ∀ i : Fin n, f i = g i) : allFin f = allFin g :=
  by grind [allFin]

def is_winning_strategy (strategy : KripkeGamePartialStrategy n) (moves : ℕ) (state : KripkeGameVisibleState n) : Bool :=
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      decide (state.possibleFramesUptoIsoCard ≤ moves)
  | .askQueryAndThen _ _, 0 =>
      false  -- Can't ask a query with no moves remaining
  | .askQueryAndThen query continuations, moves + 1 =>
      if h : continuations.size = state.frameSize + 1 then
        allFin (fun answer =>
          is_winning_strategy
            (continuations[answer]'(by simp [h]))
            moves
            (state.withNewQueryAndAnswer query answer))
      else
        false

def as_winning_strategy (strategy : KripkeGamePartialStrategy n) (moves : ℕ) (state : KripkeGameVisibleState n)
                        (h : is_winning_strategy strategy moves state = true) :
                        KripkeGameWinningStrategy moves state :=
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      KripkeGameWinningStrategy.withExhaustiveSearch (by
        unfold is_winning_strategy at h; simp_all
      )
  | .askQueryAndThen query continuations, moves + 1 =>
      have h_size : continuations.size = state.frameSize + 1 := by
        unfold is_winning_strategy at h; split at h <;> simp_all
      KripkeGameWinningStrategy.withParticularQuery query (fun answer =>
        as_winning_strategy
          (continuations[answer]'(by simp [h_size]))
          moves
          (state.withNewQueryAndAnswer query answer)
          (by
            unfold is_winning_strategy at h
            simp only [h_size, reduceDIte] at h
            exact allFin_true_then_true h answer
          )
      )

end KripkeGameStrategy
