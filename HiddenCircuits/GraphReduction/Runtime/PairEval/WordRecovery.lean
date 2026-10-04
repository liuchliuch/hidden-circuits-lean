import HiddenCircuits.Complexity.PairEncoding
import HiddenCircuits.GraphReduction.Runtime.PairEval.WordRatio
import HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericSolver

/-! Exact standalone Word→Pair interpolation. Neutral inner-loop cells contain
no oracle information; the only contributing index in every row is zero. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordRecovery
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
open scoped BigOperators

noncomputable def answer (w : WordInstance) (t : ℕ) : ℕ :=
  Layered.matchingCount (pairCuts (sampleWord w.word t)) w.source w.target

noncomputable def term (w : WordInstance) (q : Recovery.Index w) : ℤ×ℤ :=
  if q.2.val=0 then WordRatio.ratio (Recovery.degree w) q.1 (answer w q.1.val) else (0,1)

lemma ratio_value (d : ℕ) (t : Fin (d+1)) (a : ℕ) :
    RationalAccumulator.value (WordRatio.ratio d t a)=
      (a:ℚ)*(interpolationNegativeNumerator d t:ℚ)/(interpolationDenominator d t:ℚ) := by
  simp [RationalAccumulator.value,WordRatio.ratio]
lemma term_nonzero (w : WordInstance) (q : Recovery.Index w) : (term w q).2≠0 := by
  unfold term
  split_ifs
  · exact interpolationDenominator_ne_zero _ _
  · decide
lemma terms_value (w : WordInstance) :
    ((GenericDriver.terms w (term w)).map RationalAccumulator.value).sum=w.value := by
  rw [GenericDriver.terms,List.map_map,Recovery.sum_indices,Fintype.sum_sigma]
  change (∑ t : Fin (Recovery.degree w+1), ∑ s : Fin (Recovery.innerDegree w t+1), RationalAccumulator.value (term w ⟨t,s⟩))=w.value
  have hs (t : Fin (Recovery.degree w+1)) :
      (∑s : Fin (Recovery.innerDegree w t+1),RationalAccumulator.value (term w ⟨t,s⟩))=
        RationalAccumulator.value (WordRatio.ratio (Recovery.degree w) t (answer w t.val)) := by
    rw [Finset.sum_eq_single (0 : Fin (Recovery.innerDegree w t+1))]
    · simp [term]
    · intro s hs hne
      have hn : s.val≠0 := by intro h;exact hne (Fin.ext h)
      simp [term,hn,RationalAccumulator.value]
    · simp
  rw [show (∑ t : Fin (Recovery.degree w+1), ∑ s : Fin (Recovery.innerDegree w t+1), RationalAccumulator.value (term w ⟨t,s⟩)) =
      ∑ t : Fin (Recovery.degree w+1), RationalAccumulator.value (WordRatio.ratio (Recovery.degree w) t (answer w t.val)) from Finset.sum_congr rfl (fun t _ => hs t)]
  simp only [ratio_value]
  rw [←Recovery.interpolation_negative]
  simpa only [recoverWordFromPairs,pairWordMatrix_eq_matchingCount,Recovery.degree,answer,WordInstance.value] using
    recoverWordFromPairs_correct w.word w.source w.target

lemma answer_bound (w : WordInstance) (hw : w.word≠[]) (t : Fin (Recovery.degree w+1)) :
    (answer w t.val:ℤ).natAbs≤2^((Recovery.vertexBound (wordBits w).length+1)^2) := by
  let P : PairInput:=⟨w.particles,w.positive,w.source,w.target,sampleWord w.word t.val,pairedQuery_nonempty w.word hw t.val⟩
  have h:=P.value_bound
  have hp:w.particles≤(wordBits w).length:=by have := wordBits_length_lower w;omega
  have hh:Recovery.height w t≤Recovery.heightBound (wordBits w).length:=(Recovery.parameter_bounds w t).2.1
  have hv:4*w.particles*Recovery.height w t≤Recovery.vertexBound (wordBits w).length+1 := by
    have hprod:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp) hh
    have hg:1≤Recovery.heightBound (wordBits w).length+1:=by omega
    have hm:=Nat.mul_le_mul_left (4*(wordBits w).length*Recovery.heightBound (wordBits w).length) hg
    unfold Recovery.vertexBound
    nlinarith
  simp only [Int.natAbs_natCast]
  exact h.trans (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hv 2))

lemma ratio_bound (w : WordInstance) (hw : w.word≠[]) (t : Fin (Recovery.degree w+1)) :
    (WordRatio.ratio (Recovery.degree w) t (answer w t.val)).1.natAbs≤2^(Recovery.termExponent (wordBits w).length) ∧
    (WordRatio.ratio (Recovery.degree w) t (answer w t.val)).2.natAbs≤2^(Recovery.termExponent (wordBits w).length) := by
  have ho:=Recovery.weights_envelope t (Recovery.parameter_bounds w t).1
  have ha:=answer_bound w hw t
  constructor
  · have h:=Nat.mul_le_mul ha ho.1
    simp only [←pow_add] at h
    change ((answer w t.val:ℤ)*interpolationNegativeNumerator (Recovery.degree w) t).natAbs≤_
    rw [Int.natAbs_mul]
    exact h.trans (Nat.pow_le_pow_right (by decide) (by unfold Recovery.termExponent;omega))
  · exact ho.2.trans (Nat.pow_le_pow_right (by decide) (by unfold Recovery.termExponent;omega))
lemma term_bound (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w) :
    (term w q).1.natAbs≤2^(Recovery.termExponent (wordBits w).length) ∧
    (term w q).2.natAbs≤2^(Recovery.termExponent (wordBits w).length) := by
  unfold term
  split_ifs
  · exact ratio_bound w hw q.1
  · constructor
    · simp
    · exact Nat.one_le_pow _ _ (by decide)
lemma registers_bounded (w : WordInstance) (hw : w.word≠[]) (t : Fin (Recovery.degree w+1)) :
    RegisterMachine.Bounded (Driver.componentP.eval (wordBits w).length)
      (RatioCombine.registers 1 (answer w t.val:ℤ) (interpolationNegativeNumerator (Recovery.degree w) t)
        1 (interpolationDenominator (Recovery.degree w) t) 1 1) := by
  have ho:=Recovery.weights_envelope t (Recovery.parameter_bounds w t).1
  have ha:=answer_bound w hw t
  have hD:(Recovery.outerBound (wordBits w).length)^2+1≤Recovery.termExponent (wordBits w).length:=by unfold Recovery.termExponent;omega
  have hA:(Recovery.vertexBound (wordBits w).length+1)^2≤Recovery.termExponent (wordBits w).length:=by unfold Recovery.termExponent;omega
  have ha':=ha.trans (Nat.pow_le_pow_right (by decide) hA)
  have hn':=ho.1.trans (Nat.pow_le_pow_right (by decide) hD)
  have hd':=ho.2.trans (Nat.pow_le_pow_right (by decide) hD)
  intro i
  rw [Driver.componentP_eval]
  apply signedBits_length_of_abs_bound
  fin_cases i <;> dsimp only [RatioCombine.registers]
  · exact Nat.one_le_pow _ _ (by decide)
  · exact ha'
  · exact hn'
  · exact Nat.one_le_pow _ _ (by decide)
  · exact hd'
  · exact Nat.one_le_pow _ _ (by decide)
  · exact Nat.one_le_pow _ _ (by decide)
lemma initialBitBound (w : WordInstance) (hw : w.word≠[]) :
    RationalAccumulator.BitBound (Driver.accumulatorP.eval (wordBits w).length) (0,1) (GenericDriver.terms w (term w)) := by
  have h:=RationalAccumulator.bitBound_of_abs (0,1) (GenericDriver.terms w (term w)) 1
    (Recovery.termExponent (wordBits w).length) (by constructor <;> decide) (by
      intro b hb
      obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hb
      exact term_bound w hw q)
  apply h.mono
  rw [Driver.accumulatorP_eval]
  have hl:(GenericDriver.terms w (term w)).length≤Recovery.queryCountBound (wordBits w).length := by
    simpa only [GenericDriver.terms,Recovery.terms,List.length_map] using Recovery.terms_length_bound w
  nlinarith
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordRecovery
