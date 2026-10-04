import HiddenCircuits.Circuit.CompositeReduction
import HiddenCircuits.Circuit.GeometricIntegerWeights
import HiddenCircuits.Circuit.SpectralWeightData
import HiddenCircuits.Circuit.RestoringSource
import HiddenCircuits.Circuit.Runtime.DyadicScalar

/-! Exact integer-ratio recovery for the actual restoring
source circuit and the canonical physical sample words emitted by the runtime. -/
namespace HiddenCircuits.Circuit.Runtime.SourceQueryRecovery
open HiddenCircuits.Complexity
open scoped BigOperators

abbrev FirstIndex {n : ℕ} (w : List (ConstraintGate n)) := Fin (Fintype.card (SpectralIndex (forbidOccurrences w)))
abbrev SecondIndex {n : ℕ} (w : List (ConstraintGate n)) := Fin (Fintype.card (SpectralIndex (signOccurrences w)))
abbrev ThirdIndex {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :=
  Fin (2*deltaOccurrences (sampledConstraintCircuit w r.val s.val)+1)
abbrev QueryIndex {n : ℕ} (w : List (ConstraintGate n)) := Σr : FirstIndex w,Σs : SecondIndex w,ThirdIndex w r s

def degree {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) : ℕ :=
  2*deltaOccurrences (sampledConstraintCircuit w r s)
def word {n : ℕ} (hn : 0<n) (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) : WordInstance :=
  compileWordInstance hn ((sampledConstraintCircuit w r.val s.val).map (DeltaGate.compileSample u.val)) (zeroBits n) (zeroBits n)
def numerator {n : ℕ} (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) : ℤ :=
  (spectralWeightData (forbidOccurrences w) 0 r.val).1*(spectralWeightData (signOccurrences w) (-1) s.val).1*
    geometricZeroNumerator (degree w r.val s.val) u*DyadicScalar.numerator (SampleEmitter.sampleNegative w false)
def denominator {n : ℕ} (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) : ℤ :=
  (spectralWeightData (forbidOccurrences w) 0 r.val).2*(spectralWeightData (signOccurrences w) (-1) s.val).2*
    geometricBasisDenominator (degree w r.val s.val) u*(2:ℤ)^(3*a+SampleScalar.sampleExponent w r.val s.val u.val)

lemma denominator_ne_zero {n : ℕ} (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    denominator a w r s u≠0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (spectralWeightData_denominator_ne_zero _ _ _)
    (spectralWeightData_denominator_ne_zero _ _ _)) (geometricBasisDenominator_ne_zero _ _)) (pow_ne_zero _ (by norm_num))

lemma scalar_sign {n : ℕ} (w : List (ConstraintGate n)) (r s u : ℕ) :
    closedScalar ((sampledConstraintCircuit w r s).map (DeltaGate.compileSample u))=
      SampleEmitter.signValue (SampleEmitter.sampleNegative w false)/(2:ℚ)^(SampleScalar.sampleExponent w r s u) := by
  rw [SampleScalar.sampled_closedScalar_div,SampleEmitter.sampleNegative_value]
  simp [SampleEmitter.signValue]

lemma coefficient_ratio {n : ℕ} (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) :
    (numerator w r s u:ℚ)/(denominator a w r s u:ℚ)=
      (1/8:ℚ)^a*targetCoefficient (forbidOccurrences w) 0 r.val*targetCoefficient (signOccurrences w) (-1) s.val*
      ((geometricZeroNumerator (degree w r.val s.val) u:ℚ)/(geometricBasisDenominator (degree w r.val s.val) u:ℚ))*
      closedScalar ((sampledConstraintCircuit w r.val s.val).map (DeltaGate.compileSample u.val)) := by
  have hf := spectralWeightData_correct (forbidOccurrences w) 0 r.val
  have hs := spectralWeightData_correct (signOccurrences w) (-1) s.val
  norm_num only [Int.cast_zero,Int.cast_neg,Int.cast_one] at hf hs
  rw [←hf,←hs,scalar_sign]
  have hd := DyadicScalar.normalization_identity a (SampleScalar.sampleExponent w r.val s.val u.val)
    (SampleEmitter.sampleNegative w false)
  unfold numerator denominator
  push_cast at hd ⊢
  simp only [div_eq_mul_inv,mul_inv_rev] at hd ⊢
  calc
    _ = ((spectralWeightData (forbidOccurrences w) 0 r.val).1:ℚ)*
      ((spectralWeightData (signOccurrences w) (-1) s.val).1:ℚ)*
      (geometricZeroNumerator (degree w r.val s.val) u:ℚ)*
      (((spectralWeightData (forbidOccurrences w) 0 r.val).2:ℚ)⁻¹)*
      (((spectralWeightData (signOccurrences w) (-1) s.val).2:ℚ)⁻¹)*
      ((geometricBasisDenominator (degree w r.val s.val) u:ℚ)⁻¹)*
      ((DyadicScalar.numerator (SampleEmitter.sampleNegative w false):ℚ)*
        ((2:ℚ)^(3*a+SampleScalar.sampleExponent w r.val s.val u.val))⁻¹) := by ring
    _ = _ := by rw [←hd];ring

lemma geometric_sum {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) (r : FirstIndex w) (s : SecondIndex w) :
    (∑u : ThirdIndex w r s, (numerator w r s u:ℚ)*(word hn w r s u).value/(denominator a w r s u:ℚ))=
      (1/8:ℚ)^a*targetCoefficient (forbidOccurrences w) 0 r.val*targetCoefficient (signOccurrences w) (-1) s.val*
        deltaCircuitMatrix (sampledConstraintCircuit w r.val s.val) (zeroBits n) (zeroBits n) := by
  have hg := geometricInterpolate_zero_integer_weights (degree w r.val s.val)
    (fun u : ThirdIndex w r s => closedScalar ((sampledConstraintCircuit w r.val s.val).map (DeltaGate.compileSample u.val))*
      (word hn w r s u).value)
  have hc := deltaWordFormula_correct hn (sampledConstraintCircuit w r.val s.val) (zeroBits n) (zeroBits n)
  change (geometricInterpolate (degree w r.val s.val)
    (fun u : ThirdIndex w r s => closedScalar ((sampledConstraintCircuit w r.val s.val).map (DeltaGate.compileSample u.val))*
      (word hn w r s u).value)).eval 0=_ at hc
  rw [hg] at hc
  rw [←hc,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hr:=coefficient_ratio a w r s u
  calc
    _ = ((numerator w r s u:ℚ)/(denominator a w r s u:ℚ))*(word hn w r s u).value := by ring
    _ = _ := by rw [hr];ring

lemma triple_sum {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n)) :
    (∑r : FirstIndex w,∑s : SecondIndex w,∑u : ThirdIndex w r s,
      (numerator w r s u:ℚ)*(word hn w r s u).value/(denominator a w r s u:ℚ))=
      (1/8:ℚ)^a*constraintCircuitMatrix w (zeroBits n) (zeroBits n) := by
  simp_rw [geometric_sum]
  rw [←recover_constraint_circuit w (zeroBits n) (zeroBits n)]
  simp only [FirstIndex,SecondIndex] at *
  simp only [Finset.mul_sum]
  simp_rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma restoring_source_triple_sum {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    (∑r : FirstIndex (restoringIndependentProgram G).gates,
      ∑s : SecondIndex (restoringIndependentProgram G).gates,
        ∑u : ThirdIndex (restoringIndependentProgram G).gates r s,
          (numerator (restoringIndependentProgram G).gates r s u:ℚ)*
            (word hn (restoringIndependentProgram G).gates r s u).value/
            (denominator (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates r s u:ℚ))=G.independentCount := by
  rw [triple_sum,←restoringIndependentProgram_scalar]
  exact restoringIndependentProgram_correct G

lemma term_of_signed_result {n : ℕ} (hn : 0<n) (a : ℕ) (w : List (ConstraintGate n))
    (r : FirstIndex w) (s : SecondIndex w) (u : ThirdIndex w r s) (z : ℤ) (hz : (word hn w r s u).value=(z:ℚ)) :
    (((numerator w r s u*z):ℤ):ℚ)/(denominator a w r s u:ℚ)=
      (numerator w r s u:ℚ)*(word hn w r s u).value/(denominator a w r s u:ℚ) := by rw [hz,Int.cast_mul]
end HiddenCircuits.Circuit.Runtime.SourceQueryRecovery
