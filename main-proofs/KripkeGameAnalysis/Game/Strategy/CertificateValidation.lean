import KripkeGameAnalysis.Game.Strategy.FastStrategyValidation

namespace KripkeGameStrategy

/--
A certificate tree for a 4-world strategy, storing the possible frame IDs
at each node.
-/
inductive StrategyCertificate where
  | exhaustive (possibleFrames : Multiset (Fin 65536))
  | ask (possibleFrames : Multiset (Fin 65536)) (children : Array StrategyCertificate)
deriving Inhabited

namespace StrategyCertificate

def rootFrames : StrategyCertificate -> Multiset (Fin 65536)
  | .exhaustive possibleFrames => possibleFrames
  | .ask possibleFrames _ => possibleFrames

def proves (strategy : KripkeGamePartialStrategy 4) (moves : ℕ) : StrategyCertificate -> Bool
  | .exhaustive possibleFrames =>
      match strategy, moves with
      | .proceedWithExhaustiveSearch, moves =>
          decide (possibleFrames.card ≤ moves)
      | _, _ =>
          false
  | .ask possibleFrames children =>
      match strategy, moves with
      | .askQueryAndThen query continuations, moves + 1 =>
          if hcont : continuations.size = 5 then
            if hchildren : children.size = 5 then
              allFin (fun answer : Fin 5 =>
                let child := children[answer]'(by simpa [hchildren] using answer.isLt)
                let expectedFrames := (partitionPossibleFrames4 possibleFrames query)[answer.val]'(by
                  rw [partitionPossibleFrames4_size]
                  exact answer.isLt)
                decide (child.rootFrames = expectedFrames)
                  && proves (continuations[answer]'(by simpa [hcont] using answer.isLt)) moves child
              )
            else
              false
          else
            false
      | _, _ =>
          false

theorem proves_sound
    (strategy : KripkeGamePartialStrategy 4)
    (moves : ℕ)
    (certificate : StrategyCertificate)
    (h : certificate.proves strategy moves = true) :
    is_winning_strategy_on_frames strategy moves certificate.rootFrames = true := by
  induction moves generalizing strategy certificate with
  | zero =>
      cases strategy with
      | proceedWithExhaustiveSearch =>
          cases certificate with
          | exhaustive possibleFrames =>
              simpa [StrategyCertificate.proves, StrategyCertificate.rootFrames, is_winning_strategy_on_frames] using h
          | ask possibleFrames children =>
              simp [StrategyCertificate.proves] at h
      | askQueryAndThen query continuations =>
          cases certificate <;> simp [StrategyCertificate.proves] at h
  | succ moves ih =>
      cases strategy with
      | proceedWithExhaustiveSearch =>
          cases certificate with
          | exhaustive possibleFrames =>
              simpa [StrategyCertificate.proves, StrategyCertificate.rootFrames, is_winning_strategy_on_frames] using h
          | ask possibleFrames children =>
              simp [StrategyCertificate.proves] at h
      | askQueryAndThen query continuations =>
          cases certificate with
          | exhaustive possibleFrames =>
              simp [StrategyCertificate.proves] at h
          | ask possibleFrames children =>
              by_cases hcont : continuations.size = 5
              · by_cases hchildren : children.size = 5
                · simp [StrategyCertificate.proves, is_winning_strategy_on_frames, hcont, hchildren] at h ⊢
                  unfold allFin at h ⊢
                  apply List.all_eq_true.mpr
                  intro answer hAnswerMem
                  let child := children[answer]'(by simpa [hchildren] using answer.isLt)
                  let expectedFrames := (partitionPossibleFrames4 possibleFrames query)[answer.val]'(by
                    rw [partitionPossibleFrames4_size]
                    exact answer.isLt)
                  have hAnswer := List.all_eq_true.mp h answer hAnswerMem
                  simp only [child, expectedFrames, Bool.and_eq_true] at hAnswer
                  rcases hAnswer with ⟨hEq, hChild⟩
                  have hEq' : child.rootFrames = expectedFrames := by
                    simpa [child, expectedFrames] using hEq
                  have hSound := ih
                    (continuations[answer]'(by simpa [hcont] using answer.isLt))
                    child
                    hChild
                  have hSound' := hSound
                  rw [hEq'] at hSound'
                  simpa [StrategyCertificate.rootFrames, expectedFrames] using hSound'
                · simp [StrategyCertificate.proves, hcont, hchildren] at h
              · simp [StrategyCertificate.proves, hcont] at h

end StrategyCertificate

end KripkeGameStrategy
