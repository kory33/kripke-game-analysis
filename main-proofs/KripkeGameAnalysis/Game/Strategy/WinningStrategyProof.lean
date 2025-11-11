import KripkeGameAnalysis.Game.Strategy.gen.Strategy
import KripkeGameAnalysis.Game.Strategy.FastStrategyValidation

/--
A winning strategy for the Kripke game, implemented using the Rust-generated certificate.
-/
def kripkeGame_winning_strategy_impl : ∀state : KripkeGameVisibleState.InitialVisibleState 4,
                                        KripkeGameWinningStrategy 10 state.val :=
  fun state =>
    let relCount : Fin 17 := state.val.accessiblityRelationSize
    let strategy := KripkeGameAnalysis.Generated.strategyForRelationCount relCount
    -- Use the fast version of is_winning_strategy which reuses the possible frames set
    -- as we traverse the strategy tree, avoiding expensive recomputation at each leaf
    have h : KripkeGameStrategy.is_winning_strategy strategy 10 state.val = true := by
      rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
      have : state.val = (⟨state.val.accessiblityRelationSize, []⟩ : KripkeGameVisibleState 4) := by
        cases state; apply KripkeGameVisibleState.ext <;> simp_all
      rw [this]

      unfold strategy relCount
      match h : state.val.accessiblityRelationSize.val with
      | 0 => unfold KripkeGameStrategy.is_winning_strategy_fast; simp_all
      | 1 => sorry
      | 2 => sorry
      | 3 => sorry
      | 4 => sorry
      | 5 => sorry
      | 6 => sorry
      | 7 => sorry
      | 8 => sorry
      | 9 => sorry
      | 10 => sorry
      | 11 => sorry
      | 12 => sorry
      | 13 => sorry
      | 14 => sorry
      | 15 => sorry
      | 16 => sorry
      | n + 17 => omega
    KripkeGameStrategy.as_winning_strategy strategy 10 state.val h
