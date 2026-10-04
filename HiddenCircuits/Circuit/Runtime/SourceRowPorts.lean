import HiddenCircuits.Circuit.Runtime.SourceRowRuntime

/-! The spectral index and scratch ports through the fixed
word-solver bank and the clean geometric-loop clock. -/
namespace HiddenCircuits.Circuit.Runtime.SourceRow
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic

def parameterPort (k : ℕ) (i : Fin 64) : Fin (k+66) :=
  FramedFor.embedding (k+64) (SourceWordCall.lowEmbedding k i)
lemma parameter_value {k n : ℕ} (w : List (ConstraintGate n)) (a r s : ℕ) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    state (k:=k) w a r s acc (parameterPort k i)=SourceSample.store (SourceSample.canonical w a r s 0) {accumulator:=acc} i := by
  simp [state,parameterPort,SourceWordCall.lifted]
lemma parameter_injective (k : ℕ) : Function.Injective (parameterPort k) :=
  (FramedFor.embedding (k+64)).injective.comp (SourceWordCall.lowEmbedding k).injective
lemma update_r {k n : ℕ} (w : List (ConstraintGate n)) (a r s r' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (state (k:=k) w a r s acc) (parameterPort k 2) (List.replicate r' true)=state w a r' s acc := by
  unfold state parameterPort SourceWordCall.lifted
  rw [FramedFor.update_body,SourceWordCall.update_low,SourceSample.update_r]
  rfl
lemma update_s {k n : ℕ} (w : List (ConstraintGate n)) (a r s s' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (state (k:=k) w a r s acc) (parameterPort k 3) (List.replicate s' true)=state w a r s' acc := by
  unfold state parameterPort SourceWordCall.lifted
  rw [FramedFor.update_body,SourceWordCall.update_low,SourceSample.update_s]
  rfl
end HiddenCircuits.Circuit.Runtime.SourceRow
