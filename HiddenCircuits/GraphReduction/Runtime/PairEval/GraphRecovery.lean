import HiddenCircuits.Complexity.PairEncoding
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecoveryBounds

/-! One-level interpolation for an arbitrary canonical PairEval instance.
`none` selects ordinary monotone probes; `some false` and `some true` select
respectively unit-interval and private chordal-permutation even probes. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRecovery
open Complexity BinaryArithmetic WordGraph
open scoped BigOperators
abbrev Kind := Option Bool

def degree (w : PairInput) : ℕ := 2*w.particles*w.pairs.length
abbrev Index (w : PairInput) := Fin (degree w+1)
def query (kind : Kind) (w : PairInput) (s : Index w) : GraphInput :=
  match kind with
  | none => monotoneGraphInput (fun r=>w.pairs.get r) w.source w.target s.val
  | some false => unitGraphInput (fun r=>w.pairs.get r) w.source w.target (2*s.val)
  | some true => privateGraphInput (fun r=>w.pairs.get r) w.source w.target (2*s.val)
def sign (kind : Kind) (w : PairInput) : ℤ :=
  match kind with
  | some true => 1
  | _ => (-1)^(w.particles*w.pairs.length)
def numerator (kind : Kind) (w : PairInput) (s : Index w) : ℤ :=
  match kind with
  | none => interpolationNegativeNumerator (degree w) s
  | some _ => EvenWeights.numerator (degree w) s
def denominator (kind : Kind) (w : PairInput) (s : Index w) : ℤ :=
  match kind with
  | none => interpolationDenominator (degree w) s
  | some _ => EvenWeights.denominator (degree w) s
def normalization (kind : Kind) (w : PairInput) (s : Index w) : ℤ :=
  match kind with
  | none => (s.val.factorial:ℤ)^w.pairs.length
  | some false => (oddFactorial s.val:ℤ)^(w.pairs.length+1)
  | some true => (oddFactorial s.val:ℤ)^(2*w.pairs.length+1)
def ratio (kind : Kind) (w : PairInput) (s : Index w) (answer : ℕ) : ℤ×ℤ :=
  (sign kind w*(answer:ℤ)*numerator kind w s,denominator kind w s*normalization kind w s)
noncomputable def term (kind : Kind) (w : PairInput) (s : Index w) : ℤ×ℤ :=
  ratio kind w s (perfectMatchingCount (query kind w s).2.graph)
noncomputable def terms (kind : Kind) (w : PairInput) : List (ℤ×ℤ) := (List.finRange (degree w+1)).map (term kind w)

lemma denominator_ne_zero (kind : Kind) (w : PairInput) (s : Index w) : denominator kind w s≠0 := by
  cases kind with
  | none => exact interpolationDenominator_ne_zero _ _
  | some b => exact EvenWeights.denominator_ne_zero _ _
lemma normalization_ne_zero (kind : Kind) (w : PairInput) (s : Index w) : normalization kind w s≠0 := by
  cases kind with
  | none => exact pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero s.val)
  | some b => cases b <;> apply pow_ne_zero <;> exact_mod_cast (oddFactorial_pos s.val).ne'
lemma ratio_nonzero (kind : Kind) (w : PairInput) (s : Index w) (a : ℕ) : (ratio kind w s a).2≠0 :=
  mul_ne_zero (denominator_ne_zero kind w s) (normalization_ne_zero kind w s)
lemma ratio_value (kind : Kind) (w : PairInput) (s : Index w) (a : ℕ) :
    RationalAccumulator.value (ratio kind w s a)=
      (sign kind w:ℚ)*(a:ℚ)/(normalization kind w s:ℚ)*
        (numerator kind w s:ℚ)/(denominator kind w s:ℚ) := by
  simp only [RationalAccumulator.value,ratio,Int.cast_mul,Int.cast_natCast,div_eq_mul_inv,mul_inv_rev]
  ring

lemma sum_ratio_correct (kind : Kind) (w : PairInput) :
    (∑s : Index w,RationalAccumulator.value (term kind w s))=(w.value:ℚ) := by
  rw [w.value_eq_matrix]
  cases kind with
  | none =>
    rw [←recoverPairFromMonotone_correct w.pairs w.nonempty w.source w.target]
    unfold recoverPairFromMonotone recoverMonotoneTarget
    rw [Recovery.interpolation_negative,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [term,ratio_value]
    simp only [sign,numerator,denominator,normalization,query,degree,monotoneGraphInput_count,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
    ring
  | some b =>
    cases b with
    | false =>
      rw [←recoverPairFromUnitIntervals_correct w.pairs w.nonempty w.source w.target]
      unfold recoverPairFromUnitIntervals recoverUnitIntervalTarget
      rw [EvenWeights.interpolation_negative,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [term,ratio_value]
      simp only [sign,numerator,denominator,normalization,query,degree,unitGraphInput_count,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]
      ring
    | true =>
      rw [←PrivateProbe.recoverPair_correct w.pairs w.nonempty w.source w.target]
      unfold PrivateProbe.recoverPair PrivateProbe.recoverTarget
      rw [EvenWeights.interpolation_negative]
      apply Finset.sum_congr rfl
      intro s hs
      rw [term,ratio_value]
      simp only [sign,numerator,denominator,normalization,query,degree,privateGraphInput_count,Int.cast_pow,Int.cast_one,Int.cast_natCast]
      ring
lemma terms_length (kind : Kind) (w : PairInput) : (terms kind w).length=degree w+1 := by simp [terms]
lemma terms_get (kind : Kind) (w : PairInput) (s : ℕ) (hs : s<degree w+1) :
    (terms kind w)[s]?.getD (0,1)=term kind w ⟨s,hs⟩ := by
  simp [terms,List.getElem?_eq_getElem,hs]
lemma terms_value (kind : Kind) (w : PairInput) :
    ((terms kind w).map RationalAccumulator.value).sum=(w.value:ℚ) := by
  rw [terms,List.map_map,←Fin.sum_univ_def]
  exact sum_ratio_correct kind w
lemma terms_nonzero (kind : Kind) (w : PairInput) : ∀b∈terms kind w,b.2≠0 := by
  intro b hb
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hb
  exact ratio_nonzero kind w s _
lemma accumulator_nonzero (kind : Kind) (w : PairInput) :
    (RationalAccumulator.run (0,1) (terms kind w)).2≠0 :=
  RationalAccumulator.run_nonzero _ _ (by decide) (terms_nonzero kind w)
lemma accumulator_exact (kind : Kind) (w : PairInput) :
    RationalAccumulator.value (RationalAccumulator.run (0,1) (terms kind w))=(w.value:ℚ) := by
  rw [RationalAccumulator.run_value _ _ (by decide) (terms_nonzero kind w),terms_value]
  simp [RationalAccumulator.value]
lemma accumulator_product (kind : Kind) (w : PairInput) :
    (RationalAccumulator.run (0,1) (terms kind w)).1=(w.value:ℤ)*(RationalAccumulator.run (0,1) (terms kind w)).2 := by
  have h:=accumulator_exact kind w
  have hd:((RationalAccumulator.run (0,1) (terms kind w)).2:ℚ)≠0:=by exact_mod_cast accumulator_nonzero kind w
  exact_mod_cast (div_eq_iff hd).mp h
lemma accumulator_divides (kind : Kind) (w : PairInput) :
    (RationalAccumulator.run (0,1) (terms kind w)).2 ∣ (RationalAccumulator.run (0,1) (terms kind w)).1 := by
  refine ⟨(w.value:ℤ),?_⟩
  rw [accumulator_product]
  ring
lemma accumulator_quotient (kind : Kind) (w : PairInput) :
    (RationalAccumulator.run (0,1) (terms kind w)).1/(RationalAccumulator.run (0,1) (terms kind w)).2=(w.value:ℤ) := by
  rw [accumulator_product]
  exact Int.mul_ediv_cancel _ (accumulator_nonzero kind w)
end HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRecovery
