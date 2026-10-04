import HiddenCircuits.Circuit.Runtime.SpectralDeltaItems
import HiddenCircuits.Circuit.Runtime.SourceFoldBounds
import HiddenCircuits.Circuit.Runtime.SourceQueryStorage

/-! The two physical spectral loop frames and circuit-derived storage bounds.
There is no geometric interpolation clock in this native Delta runtime. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopInner
open Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

def count {n : ℕ} (w : List (ConstraintGate n)) : ℕ := Fintype.card (SpectralIndex (signOccurrences w))
lemma count_positive {n : ℕ} (w : List (ConstraintGate n)) : 0<count w := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨0,by omega⟩,⟨0,by omega⟩⟩⟩
def dataState {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) (acc : RationalAccumulator.Ratio) : Store 64 :=
  FramedFor.frame (SourceSample.store (SourceSample.canonical w 0 r s 0) {accumulator:=acc})
    (List.replicate (count w-1) true)
def state {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) (acc : RationalAccumulator.Ratio) : Store 65 :=
  FramedFor.frame (dataState w r s acc) []
def parameterPort (i : Fin 64) : Fin 65 := FramedFor.embedding 63 i
@[simp] lemma parameter_value {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    dataState w r s acc (parameterPort i)=SourceSample.store (SourceSample.canonical w 0 r s 0) {accumulator:=acc} i := by
  simp [dataState,parameterPort]
lemma update_index {n : ℕ} (w : List (ConstraintGate n)) (r s s' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (dataState w r s acc) (parameterPort 3) (List.replicate s' true)=dataState w r s' acc := by
  unfold dataState parameterPort
  rw [FramedFor.update_body,SourceSample.update_s]
  rfl

def outerPort (i : Fin 64) : Fin 66 := FramedFor.embedding 64 (parameterPort i)
@[simp] lemma outer_value {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    state w r s acc (outerPort i)=SourceSample.store (SourceSample.canonical w 0 r s 0) {accumulator:=acc} i := by
  simp [state,outerPort]
lemma update_first {n : ℕ} (w : List (ConstraintGate n)) (r s r' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (state w r s acc) (outerPort 2) (List.replicate r' true)=state w r' s acc := by
  unfold state outerPort dataState parameterPort
  rw [FramedFor.update_body,FramedFor.update_body,SourceSample.update_r]
  rfl

lemma storage_bound {n : ℕ} (w : List (ConstraintGate n)) (C : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (acc : RationalAccumulator.Ratio)
    (ha : RationalAccumulator.Bounded C acc) :
    ∀i,(SourceSample.store (SourceSample.canonical w 0 r.val s.val 0) {accumulator:=acc} i).length≤
      SourceQueryStorage.boundedStorageSize.eval ((circuitBits n w).length+C) := by
  have hc:=SourceQueryEnumeration.spectral_count_bounds w 0
  simp only [Nat.add_zero,FirstIndex,SecondIndex,Fintype.card_fin] at hc
  have hr : r.val≤((circuitBits n w).length+0+1)^2 := by have h:=r.isLt; simp only [Nat.add_zero];omega
  have hs : s.val≤((circuitBits n w).length+0+1)^2 := by have h:=s.isLt; simp only [Nat.add_zero];omega
  simpa only [Nat.add_zero] using SourceQueryStorage.polynomial_state_bound_of_indices w 0 r.val s.val 0 0 C acc
    hr hs (Nat.zero_le _) (Nat.zero_le _) ha
end HiddenCircuits.Circuit.Runtime.SpectralDeltaLoopInner

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaLoop
open Complexity OracleBlock BinaryArithmetic Polynomial SourceQueryRecovery

def count {n : ℕ} (w : List (ConstraintGate n)) : ℕ := Fintype.card (SpectralIndex (forbidOccurrences w))
lemma count_positive {n : ℕ} (w : List (ConstraintGate n)) : 0<count w := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨0,by omega⟩,⟨0,by omega⟩⟩⟩
def dataState {n : ℕ} (w : List (ConstraintGate n)) (r : ℕ) (acc : RationalAccumulator.Ratio) : Store 66 :=
  FramedFor.frame (SpectralDeltaLoopInner.state w r 0 acc) (List.replicate (count w-1) true)
def state {n : ℕ} (w : List (ConstraintGate n)) (r : ℕ) (acc : RationalAccumulator.Ratio) : Store 67 :=
  FramedFor.frame (dataState w r acc) []
def parameterPort (i : Fin 64) : Fin 67 := FramedFor.embedding 65 (SpectralDeltaLoopInner.outerPort i)
@[simp] lemma parameter_value {n : ℕ} (w : List (ConstraintGate n)) (r : ℕ) (acc : RationalAccumulator.Ratio) (i : Fin 64) :
    dataState w r acc (parameterPort i)=SourceSample.store (SourceSample.canonical w 0 r 0 0) {accumulator:=acc} i := by
  simp [dataState,parameterPort]
lemma update_index {n : ℕ} (w : List (ConstraintGate n)) (r r' : ℕ) (acc : RationalAccumulator.Ratio) :
    Function.update (dataState w r acc) (parameterPort 2) (List.replicate r' true)=dataState w r' acc := by
  unfold dataState parameterPort
  rw [FramedFor.update_body,SpectralDeltaLoopInner.update_first]
end HiddenCircuits.Circuit.Runtime.SpectralDeltaLoop
