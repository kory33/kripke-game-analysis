import KripkeGameAnalysis.Game.Strategy.Basic
import KripkeGameAnalysis.Game.Strategy.FastFiniteSemantics4

namespace KripkeGameStrategy

variable {n : ℕ}

def partitionPossibleFrames
    (possibleFrames : Multiset (Fin (2^(n^2))))
    (query : ModalFormula KripkeGameVars)
    : Array (Multiset (Fin (2^(n^2)))) :=
  let framesWithCounts : Multiset (Fin (2^(n^2)) × ℕ) := possibleFrames.map (fun frameId =>
    (frameId, (FiniteKripkeFrame.ofFin frameId).countSatisfyingNodes query))
  Array.ofFn (fun answer : Fin (n + 1) =>
    (framesWithCounts.filter (fun pair : Fin (2^(n^2)) × ℕ => pair.2 = (answer : ℕ))).map Prod.fst)

@[simp] theorem partitionPossibleFrames_size
    (possibleFrames : Multiset (Fin (2^(n^2))))
    (query : ModalFormula KripkeGameVars) :
    (partitionPossibleFrames possibleFrames query).size = n + 1 := by
  simp [partitionPossibleFrames]

@[simp] theorem partitionPossibleFrames_get
    (possibleFrames : Multiset (Fin (2^(n^2))))
    (query : ModalFormula KripkeGameVars)
    (answer : Fin (n + 1)) :
    (partitionPossibleFrames possibleFrames query)[answer] =
      ((possibleFrames.map (fun frameId =>
        (frameId, (FiniteKripkeFrame.ofFin frameId).countSatisfyingNodes query))
      ).filter (fun pair : Fin (2^(n^2)) × ℕ => pair.2 = (answer : ℕ))).map Prod.fst := by
  simp [partitionPossibleFrames]

def partitionPossibleFrames4
    (possibleFrames : Multiset (Fin 65536))
    (query : ModalFormula KripkeGameVars)
    : Array (Multiset (Fin 65536)) :=
  let framesWithCounts : Multiset (Fin 65536 × ℕ) := possibleFrames.map (fun frameId =>
    (frameId, FiniteKripkeFrame.countSatisfyingNodesFast4 (FiniteKripkeFrame.ofFin (n := 4) frameId) query))
  Array.ofFn (fun answer : Fin 5 =>
    (framesWithCounts.filter (fun pair : Fin 65536 × ℕ => pair.2 = (answer : ℕ))).map Prod.fst)

@[simp] theorem partitionPossibleFrames4_size
    (possibleFrames : Multiset (Fin 65536))
    (query : ModalFormula KripkeGameVars) :
    (partitionPossibleFrames4 possibleFrames query).size = 5 := by
  simp [partitionPossibleFrames4]

@[simp] theorem partitionPossibleFrames4_get
    (possibleFrames : Multiset (Fin 65536))
    (query : ModalFormula KripkeGameVars)
    (answer : Fin 5) :
    (partitionPossibleFrames4 possibleFrames query)[answer] =
      ((possibleFrames.map (fun frameId =>
        (frameId, FiniteKripkeFrame.countSatisfyingNodesFast4 (FiniteKripkeFrame.ofFin (n := 4) frameId) query))
      ).filter (fun pair : Fin 65536 × ℕ => pair.2 = (answer : ℕ))).map Prod.fst := by
  simp [partitionPossibleFrames4]

theorem partitionPossibleFrames4_get_eq_partitionPossibleFrames_get
    (possibleFrames : Multiset (Fin 65536))
    (query : ModalFormula KripkeGameVars)
    (answer : Fin 5) :
    (partitionPossibleFrames4 possibleFrames query)[answer] =
      (partitionPossibleFrames (n := 4) possibleFrames query)[answer] := by
  rw [partitionPossibleFrames4_get, partitionPossibleFrames_get]
  simp [FiniteKripkeFrame.countSatisfyingNodesFast4_eq]

lemma class_frameOfFin_frameToId_eq (frame : FiniteKripkeFrame.UptoIso n) :
    ⟦FiniteKripkeFrame.ofFin (FiniteKripkeFrame.UptoIso.frameToId frame)⟧ = frame := by
  simp only [FiniteKripkeFrame.UptoIso.frameToId, FiniteKripkeFrame.UptoIso.canonicalRepresentative]
  exact SetoidWithCanonicalizer.canonicalRepresentative_section_of_quot _

/-- Convert a frame ID back to its equivalence class. -/
def idToFrame (id : Fin (2^(n^2))) : FiniteKripkeFrame.UptoIso n :=
  ⟦FiniteKripkeFrame.ofFin id⟧

/--
Fast winning strategy checker that works with multisets of frame IDs for efficiency.
This is computable and avoids expensive Finset deduplication operations.

Optimization: We precompute `countSatisfyingNodes` once per frame (not once per answer),
then partition based on the precomputed counts. This avoids redundant computation.
-/
def is_winning_strategy_fast
    (strategy : KripkeGamePartialStrategy n)
    (moves : ℕ)
    (state : KripkeGameVisibleState n)
    (possibleFrames : Multiset (Fin (2^(n^2))))
    : Bool :=
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      decide (possibleFrames.card ≤ moves)
  | .askQueryAndThen _ _, 0 =>
      false
  | .askQueryAndThen query continuations, moves + 1 =>
      if h : continuations.size = state.frameSize + 1 then
        allFin (fun answer =>
          is_winning_strategy_fast
            (continuations[answer]'(by simp [h]))
            moves
            (state.withNewQueryAndAnswer query answer)
            ((partitionPossibleFrames possibleFrames query)[answer.val]'(by
              rw [partitionPossibleFrames_size]
              simpa [KripkeGameVisibleState.frameSize] using answer.isLt)))
      else
        false

/--
Specialized winning strategy checker for 4-world frames that only tracks the
current possible frame IDs.
-/
def is_winning_strategy_on_frames
    (strategy : KripkeGamePartialStrategy 4)
    (moves : ℕ)
    (possibleFrames : Multiset (Fin 65536))
    : Bool :=
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      decide (possibleFrames.card ≤ moves)
  | .askQueryAndThen _ _, 0 =>
      false
  | .askQueryAndThen query continuations, moves + 1 =>
      if h : continuations.size = 5 then
        allFin (fun answer : Fin 5 =>
          is_winning_strategy_on_frames
            (continuations[answer]'(by simp [h]))
            moves
            ((partitionPossibleFrames4 possibleFrames query)[answer.val]'(by
              rw [partitionPossibleFrames4_size]
              exact answer.isLt)))
      else
        false

theorem is_winning_strategy_on_frames_eq_fast
    (strategy : KripkeGamePartialStrategy 4)
    (moves : ℕ)
    (state : KripkeGameVisibleState 4)
    (possibleFrames : Multiset (Fin 65536))
    : is_winning_strategy_on_frames strategy moves possibleFrames
      = is_winning_strategy_fast strategy moves state possibleFrames := by
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      unfold is_winning_strategy_on_frames is_winning_strategy_fast
      rfl
  | .askQueryAndThen _ _, 0 =>
      unfold is_winning_strategy_on_frames is_winning_strategy_fast
      rfl
  | .askQueryAndThen query continuations, moves + 1 =>
      by_cases h : continuations.size = 5
      · have h' : continuations.size = state.frameSize + 1 := by
          simpa [KripkeGameVisibleState.frameSize] using h
        simp [is_winning_strategy_on_frames, is_winning_strategy_fast, h, h']
        apply allFin_ext
        intro answerCount
        have hPartition :
            ((partitionPossibleFrames4 possibleFrames query)[answerCount.val]'(by
              rw [partitionPossibleFrames4_size]
              exact answerCount.isLt)) =
            ((partitionPossibleFrames possibleFrames query)[answerCount.val]'(by
              rw [partitionPossibleFrames_size]
              exact answerCount.isLt)) := by
          simpa using partitionPossibleFrames4_get_eq_partitionPossibleFrames_get possibleFrames query answerCount
        have hRec := is_winning_strategy_on_frames_eq_fast
          (continuations[answerCount]'(by simpa [h, KripkeGameVisibleState.frameSize] using answerCount.isLt))
          moves
          (state.withNewQueryAndAnswer query answerCount)
          ((partitionPossibleFrames4 possibleFrames query)[answerCount.val]'(by
            rw [partitionPossibleFrames4_size]
            exact answerCount.isLt))
        simpa [hPartition] using hRec
      · have h' : ¬ continuations.size = state.frameSize + 1 := by
          simpa [KripkeGameVisibleState.frameSize] using h
        simp [is_winning_strategy_on_frames, is_winning_strategy_fast, h, h']

lemma idToFrame_frameToId (frame : FiniteKripkeFrame.UptoIso n) :
    idToFrame (FiniteKripkeFrame.UptoIso.frameToId frame) = frame := by
  unfold FiniteKripkeFrame.UptoIso.frameToId idToFrame
  exact SetoidWithCanonicalizer.canonicalRepresentative_section_of_quot _

lemma frameToId_injective : Function.Injective (@FiniteKripkeFrame.UptoIso.frameToId n) := by
  intro f1 f2 h
  unfold FiniteKripkeFrame.UptoIso.frameToId at h
  have h := BitVec.toFin_inj.mp h
  dsimp only [FiniteKripkeFrame.asBitVec] at h
  exact SetoidWithCanonicalizer.canonicalRepresentative.inj' h

/--
The cardinality of a multiset obtained from a finset equals the finset's cardinality.
-/
lemma Multiset.card_of_finset_val (s : Finset α) :
    s.val.card = s.card := by
  rfl

/--
Counting satisfying nodes is well-defined on quotient: works the same on
a representative frame and its equivalence class.
-/
lemma countSatisfyingNodes_ofFin_eq_quotient (id : Fin (2^(n^2))) (query : ModalFormula KripkeGameVars) :
    (FiniteKripkeFrame.ofFin id).countSatisfyingNodes query = (idToFrame id).countSatisfyingNodes query := by
  unfold idToFrame
  rfl

lemma multiset_filter_eq_iff [DecidableEq α] (s : Multiset α)
                             (p q : α → Prop) [DecidablePred p] [DecidablePred q]
                             (h : p = q) : s.filter p = s.filter q := by
  -- NOTE: I (kory33) am sure that we can eliminate [DecidableEq α] requirement, but Multiset.ext' requires it
  --       to state the equality through the result of Mutiset.count, which in turn uses DecidableEq for counting.
  --       But for our purpose, this is sufficient.
  ext a; rw [Multiset.count_filter, Multiset.count_filter]; grind

theorem is_winning_strategy_fast_eq_slow
    (strategy : KripkeGamePartialStrategy n)
    (moves : ℕ)
    (state : KripkeGameVisibleState n)
    : is_winning_strategy_fast strategy moves state (state.possibleFramesUptoIso.val.map FiniteKripkeFrame.UptoIso.frameToId)
      = is_winning_strategy strategy moves state := by
  match strategy, moves with
  | .proceedWithExhaustiveSearch, moves =>
      unfold is_winning_strategy_fast is_winning_strategy
      rw [Multiset.card_map, Multiset.card_of_finset_val]
      simp only [KripkeGameVisibleState.possibleFramesUptoIsoCard]
  | .askQueryAndThen _ _, 0 =>
      unfold is_winning_strategy_fast is_winning_strategy
      simp
  | .askQueryAndThen query continuations, moves + 1 =>
      unfold is_winning_strategy_fast is_winning_strategy
      split <;> (rename_i h)
      · unfold allFin; apply allFin_ext; intro answerCount
        rw [←is_winning_strategy_fast_eq_slow
          (continuations[answerCount]'(by simpa [h, KripkeGameVisibleState.frameSize] using answerCount.isLt))
          moves
          _]
        congr
        simp [partitionPossibleFrames, Multiset.filter_map]
        apply congrArg
        rw [KripkeGameVisibleState.withNewQueryAndAnswer_possibileFramesUptoIso]
        have : (fun (x : FiniteKripkeFrame.UptoIso n) => (FiniteKripkeFrame.ofFin (FiniteKripkeFrame.UptoIso.frameToId x)).countSatisfyingNodes query = ↑answerCount)
             = (fun (x : FiniteKripkeFrame.UptoIso n) => x.countSatisfyingNodes query = ↑answerCount) := by
          funext frameClass
          rw (occs := .pos [2]) [←class_frameOfFin_frameToId_eq frameClass]
          simp [FiniteKripkeFrame.UptoIso.countSatisfyingNodes]
        rw [multiset_filter_eq_iff _ _ _ this]
        rfl
      · rfl

end KripkeGameStrategy
