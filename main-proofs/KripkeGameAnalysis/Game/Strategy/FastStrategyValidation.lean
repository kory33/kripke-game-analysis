import KripkeGameAnalysis.Game.Strategy.Basic

namespace KripkeGameStrategy

variable {n : ℕ}

def is_winning_strategy_fast
    (strategy : KripkeGamePartialStrategy n)
    (moves : ℕ)
    (state : KripkeGameVisibleState n)
    (possibleFrames : Finset (FiniteKripkeFrame.UptoIso n))
    : Bool :=
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      decide (possibleFrames.card ≤ moves)
  | .askQueryAndThen _ _, 0 =>
      false
  | .askQueryAndThen query continuations, moves + 1 =>
      if h : continuations.size = state.frameSize + 1 then
        allFin (fun answer =>
          let newState := state.withNewQueryAndAnswer query answer
          -- Filter frames that satisfy the new query-answer constraint
          let newPossibleFrames := possibleFrames.filter (fun frame =>
            frame.countSatisfyingNodes query = (answer : ℕ))
          is_winning_strategy_fast
            (continuations[answer]'(by simp [h]))
            moves
            newState
            newPossibleFrames)
      else
        false

lemma possibleFrames_filter_eq_withNewQuery
    (state : KripkeGameVisibleState n)
    (query : ModalFormula KripkeGameVars)
    (answer : Fin (state.frameSize + 1))
    : (state.possibleFramesUptoIso.filter (fun frame =>
        frame.countSatisfyingNodes query = (answer : ℕ)))
      = (state.withNewQueryAndAnswer query answer).possibleFramesUptoIso := by
  unfold KripkeGameVisibleState.possibleFramesUptoIso
  unfold KripkeGameVisibleState.withNewQueryAndAnswer
  ext frame
  simp only [Finset.mem_filter, List.all_cons, decide_eq_true_eq, Bool.and_eq_true,
             KripkeGameVisibleState.frameSize]
  tauto

theorem is_winning_strategy_fast_eq_slow
    (strategy : KripkeGamePartialStrategy n)
    (moves : ℕ)
    (state : KripkeGameVisibleState n)
    : is_winning_strategy_fast strategy moves state state.possibleFramesUptoIso
      = is_winning_strategy strategy moves state := by
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      unfold is_winning_strategy_fast is_winning_strategy
      simp only [KripkeGameVisibleState.possibleFramesUptoIsoCard]
  | .askQueryAndThen _ _, 0 =>
      unfold is_winning_strategy_fast is_winning_strategy
      simp
  | .askQueryAndThen query continuations, moves + 1 =>
      unfold is_winning_strategy_fast is_winning_strategy
      split <;> rename_i h
      · congr 1
        funext answer
        have := is_winning_strategy_fast_eq_slow (continuations[answer]'(by simp [h])) moves (state.withNewQueryAndAnswer query answer)
        rw [← possibleFrames_filter_eq_withNewQuery] at this
        exact this
      · rfl

end KripkeGameStrategy
