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
        -- Pre-compute counts for each frame (evaluate countSatisfyingNodes only once per frame)
        let frameWithCounts : Finset (FiniteKripkeFrame.UptoIso n × ℕ) :=
          possibleFrames.image (fun frame => (frame, frame.countSatisfyingNodes query))
        -- Partition frames by their counts
        let partitionedFrames := Array.ofFn (fun answer : Fin (state.frameSize + 1) =>
          (frameWithCounts.filter (fun (_, count) => count = (answer : ℕ))).image Prod.fst)
        allFin (fun answer =>
          is_winning_strategy_fast
            (continuations[answer]'(by simp [h]))
            moves
            (state.withNewQueryAndAnswer query answer)
            (partitionedFrames[answer.val]'(by
              rw [Array.size_ofFn]
              exact answer.isLt)))
      else
        false

lemma array_ofFn_getElem (f : Fin m → α) (i : Fin m) (h : i.val < (Array.ofFn f).size) :
    (Array.ofFn f)[i]'h = f i := by
  simp [Array.getElem_ofFn]

lemma partition_via_image_eq_direct_filter
    (frames : Finset (FiniteKripkeFrame.UptoIso n))
    (query : ModalFormula KripkeGameVars)
    (answer : ℕ)
    : ((frames.image (fun frame => (frame, frame.countSatisfyingNodes query))).filter
        (fun (_, count) => count = answer)).image Prod.fst
      = frames.filter (fun frame => frame.countSatisfyingNodes query = answer) := by
  ext frame
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · -- Forward
    intro ⟨⟨f, c⟩, ⟨⟨a, h_a_mem, h_pair⟩, h_count⟩, h_fst⟩
    simp only [Prod.mk.injEq] at h_pair h_fst
    rw [← h_fst, ← h_pair.1]
    exact ⟨h_a_mem, h_pair.2 ▸ h_count⟩
  · -- Backward
    intro ⟨h_mem, h_count⟩
    refine ⟨(frame, frame.countSatisfyingNodes query), ⟨⟨frame, h_mem, rfl⟩, h_count⟩, rfl⟩

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
      · -- Expand the let bindings and show equality
        show (let frameWithCounts := state.possibleFramesUptoIso.image
                (fun frame => (frame, frame.countSatisfyingNodes query))
              let partitionedFrames := Array.ofFn (fun answer : Fin (state.frameSize + 1) =>
                (frameWithCounts.filter (fun (_, count) => count = (answer : ℕ))).image Prod.fst)
              allFin (fun answer =>
                is_winning_strategy_fast
                  (continuations[answer]'(by simp [h]))
                  moves
                  (state.withNewQueryAndAnswer query answer)
                  (partitionedFrames[answer.val]'(by rw [Array.size_ofFn]; exact answer.isLt))))
          = allFin (fun answer =>
              is_winning_strategy
                (continuations[answer]'(by simp [h]))
                moves
                (state.withNewQueryAndAnswer query answer))
        -- Expand the let bindings
        show allFin (fun answer =>
            is_winning_strategy_fast
              (continuations[answer]'(by simp [h]))
              moves
              (state.withNewQueryAndAnswer query answer)
              ((Array.ofFn (fun answer : Fin (state.frameSize + 1) =>
                ((state.possibleFramesUptoIso.image
                  (fun frame => (frame, frame.countSatisfyingNodes query))).filter
                  (fun (_, count) => count = (answer : ℕ))).image Prod.fst))[answer.val]'(by
                    rw [Array.size_ofFn]; exact answer.isLt)))
          = allFin (fun answer =>
              is_winning_strategy
                (continuations[answer]'(by simp [h]))
                moves
                (state.withNewQueryAndAnswer query answer))
        congr 1
        funext answer
        -- Show that partitionedFrames[answer.val] equals the filtered frames
        have array_eq : (Array.ofFn (fun answer : Fin (state.frameSize + 1) =>
          ((state.possibleFramesUptoIso.image
            (fun frame => (frame, frame.countSatisfyingNodes query))).filter
            (fun (_, count) => count = (answer : ℕ))).image Prod.fst))[answer.val]'(by
              rw [Array.size_ofFn]
              exact answer.isLt)
          = ((state.possibleFramesUptoIso.image
              (fun frame => (frame, frame.countSatisfyingNodes query))).filter
              (fun (_, count) => count = (answer : ℕ))).image Prod.fst := by
          apply array_ofFn_getElem
        rw [array_eq]
        -- Use the partition lemma to show this equals direct filtering
        rw [partition_via_image_eq_direct_filter]
        -- Apply induction hypothesis
        have ih := is_winning_strategy_fast_eq_slow
          (continuations[answer]'(by simp [h]))
          moves
          (state.withNewQueryAndAnswer query answer)
        rw [← possibleFrames_filter_eq_withNewQuery] at ih
        exact ih
      · rfl

end KripkeGameStrategy
