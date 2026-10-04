import HiddenCircuits.Circuit.Runtime.SourceSampleIntegers
import HiddenCircuits.Circuit.Runtime.SampleGridBounds
import HiddenCircuits.Circuit.Runtime.SourceCircuitBounds

/-! Polynomial envelopes for the actual integer
interpolation factors and signed word answers, in literal source bytes. -/
namespace HiddenCircuits.Circuit.Runtime.SourceQueryBounds
open HiddenCircuits.Complexity BinaryArithmetic Polynomial SourceQueryRecovery

noncomputable def basisSize : Polynomial ℕ := (4*X+1)*(X+1)^2+2
noncomputable def spectralSize : Polynomial ℕ := basisSize+(basisSize+1)*(X+1)^2+1
noncomputable def degreeSize : Polynomial ℕ := 8*(X+1)^3
noncomputable def geometricSize : Polynomial ℕ := (degreeSize+1)^2+2
noncomputable def wordSize : Polynomial ℕ := SampleGridBounds.wordSize
noncomputable def exponentSize : Polynomial ℕ := 3*X+wordSize
noncomputable def resultSize : Polynomial ℕ := 14*wordSize^5
noncomputable def factorSize : Polynomial ℕ := 2*spectralSize+geometricSize
noncomputable def itemExponent : Polynomial ℕ := factorSize+exponentSize+resultSize
noncomputable def countSize : Polynomial ℕ := 9*(X+1)^7
noncomputable def sourceInputSize : Polynomial ℕ := SourceCircuitEmitter.circuitSize+2*X^3

lemma spectral_bound (g : ℕ) (z : ℤ) (hz : z.natAbs≤1) (k : ℕ) :
    (spectralWeightData g z k).1.natAbs≤2^(spectralSize.eval g) ∧
    (spectralWeightData g z k).2.natAbs≤2^(spectralSize.eval g) := by
  have h := spectralWeightData_bits g z hz k
  have he : spectralSize.eval g=spectralBasisBitBound g+(spectralBasisBitBound g+1)*(g+1)^2+1 := by
    simp [spectralSize,basisSize,spectralBasisBitBound]
  rw [he]
  constructor
  · exact (Nat.size_le.mp h.2).le
  · apply (Nat.size_le.mp h.1).le.trans
    apply Nat.pow_le_pow_right (by decide)
    nlinarith

lemma occurrence_bounds {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) :
    forbidOccurrences w≤(circuitBits n w).length+a ∧ signOccurrences w≤(circuitBits n w).length+a := by
  have h := constraintOccurrences_le_length w
  have hl := (SampleEmitter.circuit_size_bounds w).2
  omega
lemma spectral_factor_bounds {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (r s : ℕ) :
    (spectralWeightData (forbidOccurrences w) 0 r).1.natAbs≤2^(spectralSize.eval ((circuitBits n w).length+a)) ∧
    (spectralWeightData (signOccurrences w) (-1) s).1.natAbs≤2^(spectralSize.eval ((circuitBits n w).length+a)) ∧
    (spectralWeightData (forbidOccurrences w) 0 r).2.natAbs≤2^(spectralSize.eval ((circuitBits n w).length+a)) ∧
    (spectralWeightData (signOccurrences w) (-1) s).2.natAbs≤2^(spectralSize.eval ((circuitBits n w).length+a)) := by
  have hf := spectral_bound (forbidOccurrences w) 0 (by decide) r
  have hs := spectral_bound (signOccurrences w) (-1) (by decide) s
  have hm1 := Nat.pow_le_pow_right (show 0<2 by decide) (polynomial_nat_eval_mono spectralSize (occurrence_bounds w a).1)
  have hm2 := Nat.pow_le_pow_right (show 0<2 by decide) (polynomial_nat_eval_mono spectralSize (occurrence_bounds w a).2)
  exact ⟨hf.1.trans hm1,hs.1.trans hm2,hf.2.trans hm1,hs.2.trans hm2⟩
lemma degree_bound {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) :
    degree w r.val s.val≤degreeSize.eval ((circuitBits n w).length+a) := by
  apply (SampleGridBounds.degree_bound w r s).trans
  simpa [degreeSize] using polynomial_nat_eval_mono degreeSize (Nat.le_add_right (circuitBits n w).length a)
lemma geometric_bounds {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (geometricZeroNumerator (degree w r.val s.val) u).natAbs≤2^(geometricSize.eval ((circuitBits n w).length+a)) ∧
    (geometricBasisDenominator (degree w r.val s.val) u).natAbs≤2^(geometricSize.eval ((circuitBits n w).length+a)) := by
  have hg := geometricZeroWeights_bits (degree w r.val s.val) u
  have he : (degree w r.val s.val+1)^2+2≤geometricSize.eval ((circuitBits n w).length+a) := by
    simp only [geometricSize,eval_add,eval_pow,eval_one,eval_ofNat]
    gcongr
    exact degree_bound w a r s
  exact ⟨(Nat.size_le.mp (by omega : _≤geometricSize.eval ((circuitBits n w).length+a))).le,
    (Nat.size_le.mp (by omega : _≤geometricSize.eval ((circuitBits n w).length+a))).le⟩
lemma word_bound {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (wordBits (word hn w r s u)).length≤wordSize.eval ((circuitBits n w).length+a) :=
  (SampleGridBounds.emission_bounds hn w r s u).1.trans
    (polynomial_nat_eval_mono wordSize (Nat.le_add_right _ _))
lemma exponent_bound {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    3*a+SampleScalar.sampleExponent w r.val s.val u.val≤exponentSize.eval ((circuitBits n w).length+a) := by
  have h := (SampleGridBounds.emission_bounds hn w r s u).2.trans
    (polynomial_nat_eval_mono wordSize (Nat.le_add_right (circuitBits n w).length a))
  dsimp only at h
  simp only [exponentSize,eval_add,eval_mul,eval_ofNat,eval_X]
  omega
lemma result_bound {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (SourceSampleIntegers.value hn w r s u).natAbs≤2^(resultSize.eval ((circuitBits n w).length+a)) := by
  have h := SourceSampleIntegers.value_size hn w r s u
  have hm := Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left (word_bound hn w a r s u) 5)
  apply (Nat.size_le.mp (Nat.le_trans (Nat.le_succ _) h)).le.trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [resultSize,eval_mul,eval_ofNat,eval_pow] using hm

lemma numerator_bound {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (numerator w r s u).natAbs≤2^(factorSize.eval ((circuitBits n w).length+a)) := by
  have hs := spectral_factor_bounds w a r.val s.val
  have hg := (geometric_bounds w a r s u).1
  have hsign : (DyadicScalar.numerator (SampleEmitter.sampleNegative w false)).natAbs=1 := by
    unfold DyadicScalar.numerator;split_ifs <;> rfl
  simpa only [numerator,Int.natAbs_mul,hsign,Nat.mul_one,factorSize,eval_add,eval_mul,eval_ofNat,
    two_mul,pow_add] using Nat.mul_le_mul (Nat.mul_le_mul hs.1 hs.2.1) hg
lemma denominator_bound {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (a : ℕ)
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (denominator a w r s u).natAbs≤2^((factorSize+exponentSize).eval ((circuitBits n w).length+a)) := by
  have hs := spectral_factor_bounds w a r.val s.val
  have hg := (geometric_bounds w a r s u).2
  have he : ((2:ℤ)^(3*a+SampleScalar.sampleExponent w r.val s.val u.val)).natAbs≤
      2^(exponentSize.eval ((circuitBits n w).length+a)) := by
    simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 from rfl] using Nat.pow_le_pow_right (show 0<2 by decide) (exponent_bound hn w a r s u)
  simpa only [denominator,Int.natAbs_mul,factorSize,eval_add,eval_mul,eval_ofNat,two_mul,pow_add] using
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hs.2.2.1 hs.2.2.2) hg) he
lemma ratio_bound {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (SourceSampleIntegers.item hn a w r s u).1.natAbs≤2^(itemExponent.eval ((circuitBits n w).length+a)) ∧
    (SourceSampleIntegers.item hn a w r s u).2.natAbs≤2^(itemExponent.eval ((circuitBits n w).length+a)) := by
  constructor
  · simp only [SourceSampleIntegers.item,Int.natAbs_mul]
    have h := Nat.mul_le_mul (numerator_bound w a r s u) (result_bound hn w a r s u)
    simp only [←pow_add] at h
    apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [itemExponent,eval_add]
    omega
  · apply (denominator_bound hn w a r s u).trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [itemExponent,eval_add]
    omega
lemma source_input_bound {n : ℕ} (G : MatrixGraph n) :
    (circuitBits n (restoringIndependentProgram G).gates).length+2*restoringSwapPairs (sourceEdges G)≤
      sourceInputSize.eval (GraphInput.encode ⟨n,G⟩).length := by
  have hn : n≤(GraphInput.encode ⟨n,G⟩).length := GraphInput.vertices_le_length ⟨n,G⟩
  have hc := (SourceCircuitEmitter.circuitSize_bound G).trans (polynomial_nat_eval_mono SourceCircuitEmitter.circuitSize hn)
  have ha := (SourceCircuitEmitter.normalization_bound G).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn 3))
  simpa only [sourceInputSize,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X] using Nat.add_le_add hc ha
end HiddenCircuits.Circuit.Runtime.SourceQueryBounds
