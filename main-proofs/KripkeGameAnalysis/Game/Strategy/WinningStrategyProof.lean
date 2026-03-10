import KripkeGameAnalysis.Game.Strategy.gen.Strategy
import KripkeGameAnalysis.Game.Strategy.FastStrategyValidation
import KripkeGameAnalysis.Game.Strategy.CertificateValidation
import KripkeGameAnalysis.Game.Strategy.gen.PrecomputedFrameSets
import KripkeGameAnalysis.Game.Strategy.gen.StrategyCertificates
import Mathlib.Data.Finset.Dedup

open KripkeGameAnalysis.Precomputed

private def initialState (relCount : Fin 17) : KripkeGameVisibleState 4 :=
  { accessiblityRelationSize := relCount, queriesAndAnswers := [] }

private theorem strategyForRelationCount_0_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨0, by decide⟩)
      10
      (initialState ⟨0, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨0, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨0, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_0_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_0_is_winning_on_frames

private theorem strategyForRelationCount_1_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨1, by decide⟩)
      10
      (initialState ⟨1, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨1, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨1, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_1_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_1_is_winning_on_frames

private theorem strategyForRelationCount_2_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨2, by decide⟩)
      10
      (initialState ⟨2, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨2, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨2, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_2_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_2_is_winning_on_frames

private theorem strategyForRelationCount_3_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨3, by decide⟩)
      10
      (initialState ⟨3, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨3, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨3, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_3_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_3_is_winning_on_frames

private theorem strategyForRelationCount_4_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨4, by decide⟩)
      10
      (initialState ⟨4, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨4, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨4, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_4_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_4_is_winning_on_frames

private theorem strategyForRelationCount_5_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨5, by decide⟩)
      10
      (initialState ⟨5, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨5, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨5, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_5_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_5_is_winning_on_frames

private theorem strategyForRelationCount_6_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨6, by decide⟩)
      10
      (initialState ⟨6, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨6, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨6, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_6_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_6_is_winning_on_frames

private theorem strategyForRelationCount_7_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨7, by decide⟩)
      10
      (initialState ⟨7, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨7, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨7, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_7_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_7_is_winning_on_frames

private theorem strategyForRelationCount_8_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨8, by decide⟩)
      10
      (initialState ⟨8, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨8, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨8, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_8_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_8_is_winning_on_frames

private theorem strategyForRelationCount_9_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨9, by decide⟩)
      10
      (initialState ⟨9, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨9, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨9, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_9_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_9_is_winning_on_frames

private theorem strategyForRelationCount_10_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨10, by decide⟩)
      10
      (initialState ⟨10, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨10, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨10, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_10_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_10_is_winning_on_frames

private theorem strategyForRelationCount_11_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨11, by decide⟩)
      10
      (initialState ⟨11, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨11, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨11, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_11_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_11_is_winning_on_frames

private theorem strategyForRelationCount_12_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨12, by decide⟩)
      10
      (initialState ⟨12, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨12, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨12, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_12_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_12_is_winning_on_frames

private theorem strategyForRelationCount_13_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨13, by decide⟩)
      10
      (initialState ⟨13, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨13, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨13, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_13_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_13_is_winning_on_frames

private theorem strategyForRelationCount_14_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨14, by decide⟩)
      10
      (initialState ⟨14, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨14, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨14, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_14_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_14_is_winning_on_frames

private theorem strategyForRelationCount_15_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨15, by decide⟩)
      10
      (initialState ⟨15, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨15, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨15, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_15_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_15_is_winning_on_frames

private theorem strategyForRelationCount_16_is_winning :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨16, by decide⟩)
      10
      (initialState ⟨16, by decide⟩) = true := by
  change KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount ⟨16, by decide⟩)
      10
      ({ accessiblityRelationSize := ⟨16, by decide⟩, queriesAndAnswers := [] } : KripkeGameVisibleState 4) = true
  rw [← KripkeGameStrategy.is_winning_strategy_fast_eq_slow]
  rw [possibleFramesUptoIso_initial_state_16_map_frameToId]
  rw [← KripkeGameStrategy.is_winning_strategy_on_frames_eq_fast]
  simpa [KripkeGameAnalysis.Generated.strategyForRelationCount, KripkeGameAnalysis.Generated.strategies] using
    KripkeGameAnalysis.Generated.strategy_for_relation_count_16_is_winning_on_frames

private theorem strategyForRelationCount_is_winning
    (relCount : Fin 17) :
    KripkeGameStrategy.is_winning_strategy
      (KripkeGameAnalysis.Generated.strategyForRelationCount relCount)
      10
      (initialState relCount) = true := by
  match relCount with
  | ⟨0, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_0_is_winning
  | ⟨1, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_1_is_winning
  | ⟨2, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_2_is_winning
  | ⟨3, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_3_is_winning
  | ⟨4, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_4_is_winning
  | ⟨5, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_5_is_winning
  | ⟨6, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_6_is_winning
  | ⟨7, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_7_is_winning
  | ⟨8, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_8_is_winning
  | ⟨9, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_9_is_winning
  | ⟨10, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_10_is_winning
  | ⟨11, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_11_is_winning
  | ⟨12, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_12_is_winning
  | ⟨13, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_13_is_winning
  | ⟨14, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_14_is_winning
  | ⟨15, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_15_is_winning
  | ⟨16, lt_witness⟩ =>
      have : (lt_witness = (by decide)) := rfl
      rw [this]
      exact strategyForRelationCount_16_is_winning
  | ⟨_+17, _⟩ => omega

/--
A winning strategy for the Kripke game, implemented using the Rust-generated certificate.
-/
def kripkeGame_winning_strategy_impl : ∀state : KripkeGameVisibleState.InitialVisibleState 4,
                                        KripkeGameWinningStrategy 10 state.val :=
  fun state =>
    let relCount : Fin 17 := state.val.accessiblityRelationSize
    let strategy := KripkeGameAnalysis.Generated.strategyForRelationCount relCount
    have h : KripkeGameStrategy.is_winning_strategy strategy 10 state.val = true := by
      have : state.val = initialState state.val.accessiblityRelationSize := by
        cases state with
        | mk val property =>
            cases val with
            | mk relCount queries =>
                cases property
                rfl
      rw [this]
      simpa [strategy, relCount] using strategyForRelationCount_is_winning relCount
    KripkeGameStrategy.as_winning_strategy strategy 10 state.val h
