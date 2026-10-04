import HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriver
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverParameters
import HiddenCircuits.GraphReduction.Runtime.WordGraph.RecoveryRegisterBounds

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriver
open Complexity OracleBlock BinaryArithmetic Polynomial

open Driver (degreeP heightP innerP vertexP componentP accumulatorP answerP queryInputP normInputP ratioTime vertexP_eval)
noncomputable def cellTime (P : Polynomial ℕ) : Polynomial ℕ :=
  P.comp queryInputP+ratioTime+AccumulatorInto.time.comp accumulatorP+answerP+7

lemma actual_cellBound (P : Polynomial ℕ) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString) (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w)
    (hg : answerValue g bytes w q=perfectMatchingCount (Recovery.query w q).2.graph) :
    cellBound P g bytes w q (componentP.eval (wordBits w).length) (accumulatorP.eval (wordBits w).length) ≤ 
      (cellTime P).eval (wordBits w).length := by
  let L := (wordBits w).length
  have hp : w.particles ≤ L := by have := wordBits_length_lower w;dsimp [L];omega
  have hd : Recovery.degree w ≤ degreeP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).1
  have hh : Recovery.height w q.1 ≤ heightP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).2.1
  have he : Recovery.innerDegree w q.1 ≤ innerP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).2.2
  have ht : q.1.val ≤ degreeP.eval L := by have := q.1.isLt;omega
  have hs : q.2.val ≤ innerP.eval L := by have := q.2.isLt;omega
  have hA : (signedBits (answerValue g bytes w q:ℤ)).length ≤ answerP.eval L := by
    rw [hg]
    have hb : (perfectMatchingCount (Recovery.query w q).2.graph:ℤ).natAbs ≤ 2^((Recovery.vertexBound L+1)^2) :=
      Recovery.query_answer_bound w hw q
    have h := signedBits_length_of_abs_bound hb
    simpa only [answerP,eval_add,eval_pow,eval_one,eval_ofNat,vertexP_eval] using h
  have hQ : L+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length ≤ queryInputP.eval L := by
    simp only [queryInputP,eval_add,eval_X]
    omega
  have hN : q.2.val+Recovery.height w q.1+w.particles ≤ normInputP.eval L := by
    simp only [normInputP,eval_add,eval_X]
    omega
  have hqtime := polynomial_nat_eval_mono P hQ
  have hotime := polynomial_nat_eval_mono GridWeightsRuntime.pairTime hd
  have hitime := polynomial_nat_eval_mono GridWeightsRuntime.pairTime he
  have hntime := polynomial_nat_eval_mono RatioNormalization.time hN
  dsimp only at hqtime hotime hitime hntime
  unfold cellBound RatioCell.costBound
  simp only [cellTime,ratioTime,eval_add,eval_mul,eval_comp,eval_ofNat]
  change P.eval (L+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length)+
    (GridWeightsRuntime.pairTime.eval (Recovery.degree w)+GridWeightsRuntime.pairTime.eval (Recovery.innerDegree w q.1)+
      RatioNormalization.time.eval (q.2.val+Recovery.height w q.1+w.particles)+
      5*(signedBits (answerValue g bytes w q:ℤ)).length+RatioCombine.time.eval (componentP.eval L)+10)+
      AccumulatorInto.time.eval (accumulatorP.eval L)+(signedBits (answerValue g bytes w q:ℤ)).length+7 ≤ _
  dsimp only [L] at *
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriver
