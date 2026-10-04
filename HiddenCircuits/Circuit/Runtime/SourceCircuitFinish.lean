import HiddenCircuits.Circuit.Runtime.SourceCircuitBounds

/-! Actual final reversal and cleanup, exposing the circuit bytes and unary
normalization exponent as the only two nonempty output registers. -/
namespace HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def finishFrame (left right : BitString) (n : ℕ) (payload stream : BitString) (swaps : ℕ) : Store 35 := fun q =>
  if q.val=0 then left else if q.val=1 then right else if q.val=9 then List.replicate n true else
  if q.val=10 then payload else if q.val=11 then stream else if q.val=12 then List.replicate swaps true else []

def outputStore (bits : BitString) (swaps : ℕ) : Store 35 := fun q =>
  if q.val=0 then bits else if q.val=1 then List.replicate swaps true else []

noncomputable def finish : OracleBlock 35 := seq (clear 0) (seq (clear 1)
  (seq (reverseOn 11 0 (by decide)) (seq (moveOn 12 1 16 (by decide) (by decide) (by decide))
    (seq (clear 9) (clear 10)))))

theorem finish_executes (g : BitString → ℕ) (a b n : ℕ) (payload stream : BitString) (swaps : ℕ) :
    finish.Executes g (store a b n payload stream swaps) (outputStore stream.reverse swaps)
      (a+b+n+payload.length+2*stream.length+6*swaps+20) := by
  have h₀ : (clear (0 : Fin 36)).Executes g (store a b n payload stream swaps)
      (store 0 b n payload stream swaps) (a+1) := by
    convert clear_executes g (0 : Fin 36) (store a b n payload stream swaps) using 1
    · funext q;fin_cases q <;> rfl
    · simp [store]
  have h₁ : (clear (1 : Fin 36)).Executes g (store 0 b n payload stream swaps)
      (store 0 0 n payload stream swaps) (b+1) := by
    convert clear_executes g (1 : Fin 36) (store 0 b n payload stream swaps) using 1
    · funext q;fin_cases q <;> rfl
    · simp [store]
  have h₂ : (reverseOn (11 : Fin 36) 0 (by decide)).Executes g (store 0 0 n payload stream swaps)
      (finishFrame stream.reverse [] n payload [] swaps) (2*stream.length+1) := by
    convert reverseOn_executes g (11 : Fin 36) 0 (by decide) (store 0 0 n payload stream swaps) using 1
    funext q;fin_cases q <;> simp [store,finishFrame]
  have h₃ : (moveOn (12 : Fin 36) 1 16 (by decide) (by decide) (by decide)).Executes g
      (finishFrame stream.reverse [] n payload [] swaps)
      (finishFrame stream.reverse (List.replicate swaps true) n payload [] 0) (6*swaps+5) := by
    convert moveOn_executes g (12 : Fin 36) 1 16 (by decide) (by decide) (by decide)
      (finishFrame stream.reverse [] n payload [] swaps) rfl using 1
    · funext q;fin_cases q <;> simp [finishFrame]
    · simp [finishFrame]
  have h₄ : (clear (9 : Fin 36)).Executes g
      (finishFrame stream.reverse (List.replicate swaps true) n payload [] 0)
      (finishFrame stream.reverse (List.replicate swaps true) 0 payload [] 0) (n+1) := by
    convert clear_executes g (9 : Fin 36) (finishFrame stream.reverse (List.replicate swaps true) n payload [] 0) using 1
    · funext q;fin_cases q <;> rfl
    · simp [finishFrame]
  have h₅ : (clear (10 : Fin 36)).Executes g
      (finishFrame stream.reverse (List.replicate swaps true) 0 payload [] 0)
      (outputStore stream.reverse swaps) (payload.length+1) := by
    convert clear_executes g (10 : Fin 36) (finishFrame stream.reverse (List.replicate swaps true) 0 payload [] 0) using 1
    funext q;fin_cases q <;> rfl
  convert seq_executes _ _ g h₀ (seq_executes _ _ g h₁ (seq_executes _ _ g h₂
    (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ h₅)))) using 1 <;> omega

lemma finish_queryFree : finish.QueryFree := seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (reverseOn_queryFree _ _ _) (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))))

end HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
