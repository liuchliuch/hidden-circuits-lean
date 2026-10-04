import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverCell
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverParameters
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryRegisterBounds

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial

noncomputable def queryInputP : Polynomial ℕ := X+degreeP+innerP+answerP
noncomputable def normInputP : Polynomial ℕ := innerP+heightP+X
noncomputable def ratioTime : Polynomial ℕ :=
  GridWeightsRuntime.pairTime.comp degreeP+GridWeightsRuntime.pairTime.comp innerP+
  RatioNormalization.time.comp normInputP+5*answerP+RatioCombine.time.comp componentP+10
noncomputable def cellTime : Polynomial ℕ :=
  QueryAnswer.time.comp queryInputP+ratioTime+AccumulatorInto.time.comp accumulatorP+answerP+7

lemma actual_cellBound (g : BitString → ℕ) (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w)
    (hg : answerValue g w q=perfectMatchingCount (Recovery.query w q).2.graph) :
    cellBound g w q (componentP.eval (wordBits w).length) (accumulatorP.eval (wordBits w).length) ≤ 
      cellTime.eval (wordBits w).length := by
  let L := (wordBits w).length
  have hp : w.particles ≤ L := by have := wordBits_length_lower w;dsimp [L];omega
  have hd : Recovery.degree w ≤ degreeP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).1
  have hh : Recovery.height w q.1 ≤ heightP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).2.1
  have he : Recovery.innerDegree w q.1 ≤ innerP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).2.2
  have ht : q.1.val ≤ degreeP.eval L := by have := q.1.isLt;omega
  have hs : q.2.val ≤ innerP.eval L := by have := q.2.isLt;omega
  have hA : (signedBits (answerValue g w q:ℤ)).length ≤ answerP.eval L := by
    rw [hg]
    have hb : (perfectMatchingCount (Recovery.query w q).2.graph:ℤ).natAbs ≤ 2^((Recovery.vertexBound L+1)^2) :=
      Recovery.query_answer_bound w hw q
    have h := signedBits_length_of_abs_bound hb
    simpa only [answerP,eval_add,eval_pow,eval_one,eval_ofNat,vertexP_eval] using h
  have hQ : L+q.1.val+q.2.val+(signedBits (answerValue g w q:ℤ)).length ≤ queryInputP.eval L := by
    simp only [queryInputP,eval_add,eval_X]
    omega
  have hN : q.2.val+Recovery.height w q.1+w.particles ≤ normInputP.eval L := by
    simp only [normInputP,eval_add,eval_X]
    omega
  have hqtime := polynomial_nat_eval_mono QueryAnswer.time hQ
  have hotime := polynomial_nat_eval_mono GridWeightsRuntime.pairTime hd
  have hitime := polynomial_nat_eval_mono GridWeightsRuntime.pairTime he
  have hntime := polynomial_nat_eval_mono RatioNormalization.time hN
  dsimp only at hqtime hotime hitime hntime
  unfold cellBound RatioCell.costBound
  simp only [cellTime,ratioTime,eval_add,eval_mul,eval_comp,eval_ofNat]
  change QueryAnswer.time.eval (L+q.1.val+q.2.val+(signedBits (answerValue g w q:ℤ)).length)+
    (GridWeightsRuntime.pairTime.eval (Recovery.degree w)+GridWeightsRuntime.pairTime.eval (Recovery.innerDegree w q.1)+
      RatioNormalization.time.eval (q.2.val+Recovery.height w q.1+w.particles)+
      5*(signedBits (answerValue g w q:ℤ)).length+RatioCombine.time.eval (componentP.eval L)+10)+
      AccumulatorInto.time.eval (accumulatorP.eval L)+(signedBits (answerValue g w q:ℤ)).length+7 ≤ _
  dsimp only [L] at *
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
