import HiddenCircuits.Circuit.Runtime.SourceMiddleRuntime

/-! Preserve the two inner clocks and the second-spectral
master while the outer spectral index changes in the actual fixed register bank. -/
namespace HiddenCircuits.Circuit.Runtime.SourceMiddle
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic

def outerPort (k : ℕ) (i : Fin 64) : Fin (k+68) := FramedFor.embedding (k+66) (parameterPort k i)
lemma outer_value {k n : ℕ} (w : List (ConstraintGate n)) (a r s : ℕ) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    state (k:=k) w a r s acc (outerPort k i)=SourceSample.store (SourceSample.canonical w a r s 0) {accumulator:=acc} i := by
  simp [state,outerPort,parameter_value]
lemma update_first {k n : ℕ} (w : List (ConstraintGate n)) (a r s r' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (state (k:=k) w a r s acc) (outerPort k 2) (List.replicate r' true)=state w a r' s acc := by
  unfold state outerPort
  rw [FramedFor.update_body]
  unfold dataState parameterPort
  rw [FramedFor.update_body,SourceRow.update_r]
end HiddenCircuits.Circuit.Runtime.SourceMiddle

namespace HiddenCircuits.Circuit.Runtime.SourceOuter
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

def count {n : ℕ} (w : List (ConstraintGate n)) : ℕ := Fintype.card (SpectralIndex (forbidOccurrences w))
lemma count_positive {n : ℕ} (w : List (ConstraintGate n)) : 0<count w := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨0,by omega⟩,⟨0,by omega⟩⟩⟩
def dataState {k n : ℕ} (w : List (ConstraintGate n)) (a r : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+68) :=
  FramedFor.frame (SourceMiddle.state (k:=k) w a r 0 acc) (List.replicate (count w-1) true)
def state {k n : ℕ} (w : List (ConstraintGate n)) (a r : ℕ) (acc : RationalAccumulator.Ratio) : Store (k+69) :=
  FramedFor.frame (dataState (k:=k) w a r acc) []
def parameterPort (k : ℕ) (i : Fin 64) : Fin (k+69) := FramedFor.embedding (k+67) (SourceMiddle.outerPort k i)
noncomputable def body {k : ℕ} (W : OracleBlock k) : OracleBlock (k+68) := rename (SourceMiddle.program W) (FramedFor.embedding (k+67))
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+69) :=
  FramedFor.program (Fin.last (k+68)) (parameterPort k 2) (parameterPort k 24)
    (Ne.symm (FramedFor.body_ne_clock (SourceMiddle.outerPort k 24))) (body W)
noncomputable def result {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) (acc : RationalAccumulator.Ratio) : RationalAccumulator.Ratio :=
  RationalAccumulator.run acc (SourceSampleIntegers.items hn a w)
noncomputable def time (p : Polynomial ℕ) : Polynomial ℕ := (X+1)^2*(SourceMiddle.time p+5)+6*(X+1)^2+12

lemma parameter_value {k n : ℕ} (w : List (ConstraintGate n)) (a r : ℕ) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    dataState (k:=k) w a r acc (parameterPort k i)=SourceSample.store (SourceSample.canonical w a r 0 0) {accumulator:=acc} i := by
  simp [dataState,parameterPort,SourceMiddle.outer_value]
lemma update_index {k n : ℕ} (w : List (ConstraintGate n)) (a r r' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (dataState (k:=k) w a r acc) (parameterPort k 2) (List.replicate r' true)=dataState w a r' acc := by
  unfold dataState parameterPort
  rw [FramedFor.update_body,SourceMiddle.update_first]
end HiddenCircuits.Circuit.Runtime.SourceOuter
