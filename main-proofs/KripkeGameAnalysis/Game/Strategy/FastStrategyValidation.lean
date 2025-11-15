import KripkeGameAnalysis.Game.Strategy.Basic

namespace KripkeGameStrategy

variable {n : ℕ}

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
        -- Optimization: Precompute countSatisfyingNodes once per frame (not once per answer)
        -- Use Multiset.map to compute counts (computable!)
        let framesWithCounts := possibleFrames.map (fun frameId =>
          (frameId, (FiniteKripkeFrame.ofFin frameId).countSatisfyingNodes query))

        -- Partition frames by their precomputed counts
        let partitionedFrames := Array.ofFn (fun answer : Fin (state.frameSize + 1) =>
          (framesWithCounts.filter (fun pair => pair.2 = (answer : ℕ))).map Prod.fst)

        allFin (fun answer =>
          is_winning_strategy_fast
            (continuations[answer]'(by simp [h]))
            moves
            (state.withNewQueryAndAnswer query answer)
            (partitionedFrames[answer.val]'(by grind [Array.size_ofFn])))
      else
        false

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
        rw [←is_winning_strategy_fast_eq_slow continuations[answerCount] moves _]
        congr
        simp [Multiset.filter_map]
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
