import HiddenCircuits.GraphReduction.WordReductions
import HiddenCircuits.GraphReduction.QueryEncoding
import HiddenCircuits.Complexity.WordEncoding
import HiddenCircuits.Complexity.InterpolationWeights
import HiddenCircuits.Complexity.BinaryArithmetic.RationalAccumulator

/-! Fresh reconstruction: the literal nested graph-query index and integer
ratios used by the finite WordEval interpolation driver. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Recovery
open Complexity BinaryArithmetic
open scoped BigOperators

def degree (w : WordInstance) : ℕ := w.word.length*w.particles^2
def height (w : WordInstance) (t : Fin (degree w+1)) : ℕ := (sampleWord w.word t.val).length
def innerDegree (w : WordInstance) (t : Fin (degree w+1)) : ℕ := 2*w.particles*height w t
abbrev Index (w : WordInstance) := Σ t : Fin (degree w+1), Fin (innerDegree w t+1)
def indices (w : WordInstance) : List (Index w) :=
  (List.finRange (degree w+1)).sigma (fun t => List.finRange (innerDegree w t+1))
def query (w : WordInstance) (q : Index w) : GraphInput :=
  monotoneGraphInput (fun r => (sampleWord w.word q.1.val).get r) w.source w.target q.2.val

def ratio (w : WordInstance) (q : Index w) (answer : ℕ) : ℤ×ℤ :=
  (((-1:ℤ)^(w.particles*height w q.1))*(answer:ℤ)*
      interpolationNegativeNumerator (degree w) q.1*interpolationNegativeNumerator (innerDegree w q.1) q.2,
    interpolationDenominator (degree w) q.1*interpolationDenominator (innerDegree w q.1) q.2*
      (q.2.val.factorial:ℤ)^(height w q.1))
noncomputable def terms (w : WordInstance) : List (ℤ×ℤ) :=
  (indices w).map (fun q => ratio w q (perfectMatchingCount (query w q).2.graph))

lemma ratio_nonzero (w : WordInstance) (q : Index w) (answer : ℕ) : (ratio w q answer).2≠0 := by
  apply mul_ne_zero (mul_ne_zero (interpolationDenominator_ne_zero _ _) (interpolationDenominator_ne_zero _ _))
  apply pow_ne_zero
  exact_mod_cast Nat.factorial_ne_zero q.2.val
lemma terms_nonzero (w : WordInstance) : ∀b∈terms w,b.2≠0 := by
  intro b hb
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hb
  exact ratio_nonzero _ _ _

lemma interpolation_negative (d : ℕ) (f : Fin (d+1) → ℚ) :
    (interpolateValues d f).eval (-1)=∑i, f i*(interpolationNegativeNumerator d i:ℚ)/(interpolationDenominator d i:ℚ) := by
  simp only [interpolateValues,Lagrange.interpolate_apply,Polynomial.eval_finset_sum,
    Polynomial.eval_mul,Polynomial.eval_C,basis_negative_integer_weight,div_eq_mul_inv,mul_assoc]

lemma ratio_value (w : WordInstance) (q : Index w) (answer : ℕ) :
    RationalAccumulator.value (ratio w q answer)=
      (((-1:ℚ)^(w.particles*height w q.1))*(answer:ℚ)/(q.2.val.factorial:ℚ)^(height w q.1)*
      (interpolationNegativeNumerator (innerDegree w q.1) q.2:ℚ)/(interpolationDenominator (innerDegree w q.1) q.2:ℚ))*
      (interpolationNegativeNumerator (degree w) q.1:ℚ)/(interpolationDenominator (degree w) q.1:ℚ) := by
  simp only [RationalAccumulator.value,ratio,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma sum_ratio_correct (w : WordInstance) (hw : w.word≠[]) :
    (∑q : Index w, RationalAccumulator.value (ratio w q (perfectMatchingCount (query w q).2.graph)))=w.value := by
  rw [←recoverWordFromMonotone_correct w]
  unfold recoverWordFromMonotone recoverWordViaPairs
  rw [if_neg hw,interpolation_negative]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  simp only [recoverPairFromMonotone,recoverMonotoneTarget,interpolation_negative,wordPairSample]
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  rw [ratio_value]
  simp only [query,monotoneGraphInput_count]
  dsimp only [degree,height,innerDegree]
  ring

lemma sum_indices (w : WordInstance) (f : Index w → ℚ) :
    ((indices w).map f).sum=∑q,f q := by
  unfold indices List.sigma
  rw [List.map_flatMap]
  simp only [List.map_map,Function.comp_def]
  rw [List.flatMap_def,List.sum_flatten,List.map_map]
  simp only [Function.comp_def,←Fin.sum_univ_def,Fintype.sum_sigma]

lemma terms_value (w : WordInstance) (hw : w.word≠[]) :
    ((terms w).map RationalAccumulator.value).sum=w.value := by
  rw [terms,List.map_map]
  exact (sum_indices w _).trans (sum_ratio_correct w hw)

lemma accumulator_nonzero (w : WordInstance) : (RationalAccumulator.run (0,1) (terms w)).2≠0 :=
  RationalAccumulator.run_nonzero _ _ (by decide) (terms_nonzero w)
lemma accumulator_exact (w : WordInstance) (hw : w.word≠[]) :
    RationalAccumulator.value (RationalAccumulator.run (0,1) (terms w))=w.value := by
  rw [RationalAccumulator.run_value _ _ (by decide) (terms_nonzero w),terms_value w hw]
  simp [RationalAccumulator.value]
lemma accumulator_exact_product (w : WordInstance) (hw : w.word≠[]) (z : ℤ) (hz : w.value=(z:ℚ)) :
    (RationalAccumulator.run (0,1) (terms w)).1=z*(RationalAccumulator.run (0,1) (terms w)).2 := by
  have h := (accumulator_exact w hw).trans hz
  have hd : ((RationalAccumulator.run (0,1) (terms w)).2:ℚ)≠0 := by exact_mod_cast accumulator_nonzero w
  exact_mod_cast (div_eq_iff hd).mp h
lemma accumulator_divides (w : WordInstance) (hw : w.word≠[]) :
    (RationalAccumulator.run (0,1) (terms w)).2 ∣ (RationalAccumulator.run (0,1) (terms w)).1 := by
  obtain ⟨z,hz,_⟩ := word_value_bits_input w
  refine ⟨z,?_⟩
  rw [accumulator_exact_product w hw z hz]
  ring
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Recovery
