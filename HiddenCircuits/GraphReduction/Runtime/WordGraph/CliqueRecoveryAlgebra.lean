import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryAlgebra
import HiddenCircuits.Complexity.EvenWeights

/-! Fresh reconstruction: exact even-probe interpolation ratios for the actual
unit-interval and private chordal-permutation target graphs. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecovery
open Complexity BinaryArithmetic
open scoped BigOperators

def normalizationExponent (mode : Bool) (h : ℕ) : ℕ := if mode then 2*h+1 else h+1
def signExponent (mode : Bool) (p h : ℕ) : ℕ := if mode then 0 else p*h
def query (mode : Bool) (w : WordInstance) (q : Recovery.Index w) : GraphInput :=
  if mode then privateGraphInput (fun r => (sampleWord w.word q.1.val).get r) w.source w.target (2*q.2.val)
  else unitGraphInput (fun r => (sampleWord w.word q.1.val).get r) w.source w.target (2*q.2.val)
lemma query_count_false (w : WordInstance) (q : Recovery.Index w) :
    perfectMatchingCount (query false w q).2.graph=perfectMatchingCount
      (unitIntervalQueryGraph (fun r => (sampleWord w.word q.1.val).get r) w.source w.target (2*q.2.val)) :=
  unitGraphInput_count _ _ _ _
lemma query_count_true (w : WordInstance) (q : Recovery.Index w) :
    perfectMatchingCount (query true w q).2.graph=perfectMatchingCount
      (PrivateProbe.retainedQueryGraph (fun r => (sampleWord w.word q.1.val).get r) w.source w.target (2*q.2.val)) :=
  privateGraphInput_count _ _ _ _
def ratio (mode : Bool) (w : WordInstance) (q : Recovery.Index w) (answer : ℕ) : ℤ×ℤ :=
  (((-1:ℤ)^signExponent mode w.particles (Recovery.height w q.1))*(answer:ℤ)*
      interpolationNegativeNumerator (Recovery.degree w) q.1*EvenWeights.numerator (Recovery.innerDegree w q.1) q.2,
    interpolationDenominator (Recovery.degree w) q.1*EvenWeights.denominator (Recovery.innerDegree w q.1) q.2*
      (oddFactorial q.2.val:ℤ)^(normalizationExponent mode (Recovery.height w q.1)))
noncomputable def terms (mode : Bool) (w : WordInstance) : List (ℤ×ℤ) :=
  (Recovery.indices w).map (fun q => ratio mode w q (perfectMatchingCount (query mode w q).2.graph))

lemma ratio_nonzero (mode : Bool) (w : WordInstance) (q : Recovery.Index w) (answer : ℕ) :
    (ratio mode w q answer).2≠0 := by
  apply mul_ne_zero (mul_ne_zero (interpolationDenominator_ne_zero _ _) (EvenWeights.denominator_ne_zero _ _))
  apply pow_ne_zero
  exact_mod_cast (oddFactorial_pos q.2.val).ne'
lemma ratio_value (mode : Bool) (w : WordInstance) (q : Recovery.Index w) (answer : ℕ) :
    RationalAccumulator.value (ratio mode w q answer)=
      (((-1:ℚ)^signExponent mode w.particles (Recovery.height w q.1))*(answer:ℚ)/
        (oddFactorial q.2.val:ℚ)^normalizationExponent mode (Recovery.height w q.1)*
        (EvenWeights.numerator (Recovery.innerDegree w q.1) q.2:ℚ)/(EvenWeights.denominator (Recovery.innerDegree w q.1) q.2:ℚ))*
      (interpolationNegativeNumerator (Recovery.degree w) q.1:ℚ)/(interpolationDenominator (Recovery.degree w) q.1:ℚ) := by
  simp only [RationalAccumulator.value,ratio,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
lemma sum_ratio_correct (mode : Bool) (w : WordInstance) (hw : w.word≠[]) :
    (∑q:Recovery.Index w,RationalAccumulator.value (ratio mode w q (perfectMatchingCount (query mode w q).2.graph)))=w.value := by
  cases mode with
  | false =>
    rw [←recoverWordFromUnitIntervals_correct w]
    unfold recoverWordFromUnitIntervals recoverWordViaPairs
    rw [if_neg hw,Recovery.interpolation_negative,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [recoverPairFromUnitIntervals,recoverUnitIntervalTarget,EvenWeights.interpolation_negative,wordPairSample]
    simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    rw [ratio_value]
    rw [query_count_false]
    simp only [signExponent,normalizationExponent,Bool.false_eq_true,↓reduceIte]
    all_goals dsimp only [Recovery.degree,Recovery.height,Recovery.innerDegree]
    all_goals ring
  | true =>
    rw [←recoverWordFromChordalPermutation_correct w]
    unfold recoverWordFromChordalPermutation recoverWordViaPairs
    rw [if_neg hw,Recovery.interpolation_negative,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [PrivateProbe.recoverPair,PrivateProbe.recoverTarget,EvenWeights.interpolation_negative,wordPairSample]
    simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    rw [ratio_value]
    rw [query_count_true]
    simp only [signExponent,normalizationExponent,↓reduceIte,pow_zero,one_mul]
    all_goals dsimp only [Recovery.degree,Recovery.height,Recovery.innerDegree]
    all_goals ring
lemma terms_value (mode : Bool) (w : WordInstance) (hw : w.word≠[]) :
    ((terms mode w).map RationalAccumulator.value).sum=w.value := by
  rw [terms,List.map_map]
  exact (Recovery.sum_indices w _).trans (sum_ratio_correct mode w hw)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecovery
