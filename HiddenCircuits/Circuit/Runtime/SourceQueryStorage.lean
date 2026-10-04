import HiddenCircuits.Circuit.Runtime.SourceQueryEnumeration
import HiddenCircuits.Circuit.Runtime.SourceSampleFrame

/-! Bounds for the real serialized spectral tables,
all canonical low-bank stacks and every source-grid accumulator prefix. -/
namespace HiddenCircuits.Circuit.Runtime.SourceQueryStorage
open HiddenCircuits.Complexity BinaryArithmetic Polynomial SourceQueryRecovery
open SourceQueryBounds SourceQueryEnumeration SourceSampleIntegers

noncomputable def vectorSize : Polynomial ℕ := basisSize*(X+1)^2+basisSize+(X+1)^2+2
noncomputable def numeratorStreamSize : Polynomial ℕ := (X+1)^2*(2*vectorSize+2)
noncomputable def storageSize : Polynomial ℕ := X+(X+1)^2+degreeSize+numeratorStreamSize+spectralSize+5
noncomputable def boundedStorageSize : Polynomial ℕ := X+storageSize
noncomputable def prefixStorageSize : Polynomial ℕ := storageSize+accumulatorExponent+2

lemma numerator_stream_bound (g : ℕ) (mode : Bool) :
    (SpectralWeightsProgram.numeratorStream g mode).length≤numeratorStreamSize.eval g := by
  have h:=SpectralWeights.vector_stream_bound g (SpectralTargets.base mode)
    (SpectralWeightsProgram.base_abs mode) (spectralIndices g)
    (by rw [spectralIndices_length];exact spectralIndex_card_bound g)
  simpa only [SpectralWeightsProgram.numeratorStream,numeratorStreamSize,vectorSize,basisSize,
    SpectralWeights.vectorBitBound,SpectralWeights.termExponent,SpectralWeights.denominatorExponent,
    spectralBasisBitBound,eval_mul,eval_add,eval_pow,eval_X,eval_one,eval_ofNat] using h
lemma denominator_word_bound (g : ℕ) :
    (signedBits (SpectralWeights.denominator g)).length≤spectralSize.eval g+2 := by
  have h:=(spectral_bound g 0 (by decide) 0).2
  exact signedBits_length_of_abs_bound h

set_option maxHeartbeats 800000 in
lemma state_bound {n : ℕ} (w : List (ConstraintGate n)) (a r s u d A : ℕ)
    (acc : RationalAccumulator.Ratio)
    (hr : r≤((circuitBits n w).length+a+1)^2)
    (hs : s≤((circuitBits n w).length+a+1)^2)
    (hu : u≤degreeSize.eval ((circuitBits n w).length+a)+1)
    (hd : d≤degreeSize.eval ((circuitBits n w).length+a))
    (ha : RationalAccumulator.Bounded A acc) :
    ∀i,(SourceSample.store (SourceSample.canonical w a r s u)
      {accumulator:=acc,degree:=d} i).length≤A+storageSize.eval ((circuitBits n w).length+a) := by
  have ho:=occurrence_bounds w a
  have hf:=(numerator_stream_bound (forbidOccurrences w) false).trans
    (polynomial_nat_eval_mono numeratorStreamSize ho.1)
  have hz:=(numerator_stream_bound (signOccurrences w) true).trans
    (polynomial_nat_eval_mono numeratorStreamSize ho.2)
  have hfd:=(denominator_word_bound (forbidOccurrences w)).trans
    (Nat.add_le_add_right (polynomial_nat_eval_mono spectralSize ho.1) 2)
  have hzd:=(denominator_word_bound (signOccurrences w)).trans
    (Nat.add_le_add_right (polynomial_nat_eval_mono spectralSize ho.2) 2)
  dsimp only at hf hz hfd hzd
  intro i
  simp only [storageSize,eval_add,eval_X,eval_pow,eval_one,eval_ofNat]
  fin_cases i
  · change (circuitBits n w).length≤_
    omega
  · change (List.replicate (a) true).length≤_
    rw [List.length_replicate]
    omega
  · change (List.replicate (r) true).length≤_
    rw [List.length_replicate]
    omega
  · change (List.replicate (s) true).length≤_
    rw [List.length_replicate]
    omega
  · change (List.replicate (u) true).length≤_
    rw [List.length_replicate]
    omega
  · change (List.replicate (forbidOccurrences w) true).length≤_
    rw [List.length_replicate]
    omega
  · change (List.replicate (signOccurrences w) true).length≤_
    rw [List.length_replicate]
    omega
  · change (SpectralWeightsProgram.numeratorStream (forbidOccurrences w) false).length≤_
    omega
  · change (SpectralWeightsProgram.numeratorStream (signOccurrences w) true).length≤_
    omega
  · change (signedBits (SpectralWeights.denominator (forbidOccurrences w))).length≤_
    omega
  · change (signedBits (SpectralWeights.denominator (signOccurrences w))).length≤_
    omega
  · change (signedBits acc.1).length≤_
    exact ha.1.trans (by omega)
  · change (signedBits acc.2).length≤_
    exact ha.2.trans (by omega)
  · change (List.replicate (d) true).length≤_
    rw [List.length_replicate]
    omega
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 1≤_
    omega
  · change 1≤_
    omega
  · change 1≤_
    omega
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _
  · change 0≤_
    exact Nat.zero_le _

lemma sample_state_bound {n : ℕ} (w : List (ConstraintGate n)) (a A : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s)
    (acc : RationalAccumulator.Ratio) (ha : RationalAccumulator.Bounded A acc) :
    ∀i,(SourceSample.store (SourceSample.canonical w a r.val s.val u.val)
      {accumulator:=acc,degree:=degree w r.val s.val} i).length≤
      A+storageSize.eval ((circuitBits n w).length+a) := by
  have hc:=spectral_count_bounds w a
  have hr:r.val≤((circuitBits n w).length+a+1)^2 := by have h:=r.isLt;simp only [FirstIndex,Fintype.card_fin] at hc;omega
  have hs:s.val≤((circuitBits n w).length+a+1)^2 := by have h:=s.isLt;simp only [SecondIndex,Fintype.card_fin] at hc;omega
  have hu:u.val≤degreeSize.eval ((circuitBits n w).length+a) := by
    have h:=u.isLt;change u.val<degree w r.val s.val+1 at h;have hb:=degree_bound w a r s;omega
  exact state_bound w a r.val s.val u.val (degree w r.val s.val) A acc hr hs (hu.trans (Nat.le_succ _)) (degree_bound w a r s) ha

lemma polynomial_state_bound {n : ℕ} (w : List (ConstraintGate n)) (a C : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s)
    (acc : RationalAccumulator.Ratio) (ha : RationalAccumulator.Bounded C acc) :
    ∀i,(SourceSample.store (SourceSample.canonical w a r.val s.val u.val)
      {accumulator:=acc,degree:=degree w r.val s.val} i).length≤
      boundedStorageSize.eval ((circuitBits n w).length+a+C) := by
  have hm:=polynomial_nat_eval_mono storageSize (Nat.le_add_right ((circuitBits n w).length+a) C)
  dsimp only at hm
  intro i
  apply (sample_state_bound w a C r s u acc ha i).trans
  simp only [boundedStorageSize,eval_add,eval_X]
  omega

lemma polynomial_state_bound_of_indices {n : ℕ} (w : List (ConstraintGate n)) (a r s u d C : ℕ)
    (acc : RationalAccumulator.Ratio)
    (hr : r≤((circuitBits n w).length+a+1)^2)
    (hs : s≤((circuitBits n w).length+a+1)^2)
    (hu : u≤degreeSize.eval ((circuitBits n w).length+a)+1)
    (hd : d≤degreeSize.eval ((circuitBits n w).length+a))
    (ha : RationalAccumulator.Bounded C acc) :
    ∀i,(SourceSample.store (SourceSample.canonical w a r s u)
      {accumulator:=acc,degree:=d} i).length≤
      boundedStorageSize.eval ((circuitBits n w).length+a+C) := by
  have hm:=polynomial_nat_eval_mono storageSize (Nat.le_add_right ((circuitBits n w).length+a) C)
  dsimp only at hm
  intro i
  apply (state_bound w a r s u d C acc hr hs hu hd ha i).trans
  simp only [boundedStorageSize,eval_add,eval_X]
  omega

lemma prefix_state_bound {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a A j : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s)
    (acc : RationalAccumulator.Ratio) (ha : acc.1.natAbs≤2^A ∧ acc.2.natAbs≤2^A) :
    ∀i,(SourceSample.store (SourceSample.canonical w a r.val s.val u.val)
      {accumulator:=RationalAccumulator.run acc ((items hn a w).take j),degree:=degree w r.val s.val} i).length≤
      A+prefixStorageSize.eval ((circuitBits n w).length+a) := by
  have h:=prefix_abs_bound hn a w acc A j ha
  have hb:RationalAccumulator.Bounded (A+accumulatorExponent.eval ((circuitBits n w).length+a)+2)
      (RationalAccumulator.run acc ((items hn a w).take j)) :=
    ⟨signedBits_length_of_abs_bound h.1,signedBits_length_of_abs_bound h.2⟩
  intro i
  apply (sample_state_bound w a _ r s u _ hb i).trans
  simp only [prefixStorageSize,eval_add,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SourceQueryStorage
