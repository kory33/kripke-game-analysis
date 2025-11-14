import KripkeGameAnalysis.Game.Strategy.gen.Strategy
import KripkeGameAnalysis.Game.Strategy.FastStrategyValidation
import KripkeGameAnalysis.Game.Strategy.gen.PrecomputedFrameSets

open KripkeGameAnalysis.Precomputed

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
      match state.val.accessiblityRelationSize with
      | ⟨0, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_0]; clear * -;
          native_decide
      | ⟨1, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_1]; clear * -;
          native_decide
      | ⟨2, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_2]; clear * -;
          native_decide
      | ⟨3, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_3]; clear * -;
          sorry
      | ⟨4, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_4]; clear * -;
          sorry
      | ⟨5, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_5]; clear * -;
          sorry
      | ⟨6, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_6]; clear * -;
          sorry
      | ⟨7, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_7]; clear * -;
          sorry
      | ⟨8, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_8]; clear * -;
          sorry
      | ⟨9, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_9]; clear * -;
          sorry
      | ⟨10, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_10]; clear * -;
          sorry
      | ⟨11, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_11]; clear * -;
          sorry
      | ⟨12, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_12]; clear * -;
          sorry
      | ⟨13, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_13]; clear * -;
          sorry
      | ⟨14, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_14]; clear * -;
          native_decide
      | ⟨15, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_15]; clear * -;
          native_decide
      | ⟨16, lt_witness⟩ =>
          have : (lt_witness = (by decide)) := rfl; rw [this, possibleFramesUptoIso_initial_state_16]; clear * -;
          native_decide
      | ⟨_+17, _⟩ => omega
    KripkeGameStrategy.as_winning_strategy strategy 10 state.val h
