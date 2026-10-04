import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRecoveryBounds

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver
open Complexity OracleBlock BinaryArithmetic Polynomial

noncomputable def vertexP : Polynomial ℕ := 8*X*Driver.heightP*(Driver.heightP+2)
noncomputable def termP : Polynomial ℕ :=
  (vertexP+1)^2+Driver.degreeP^2+2*Driver.innerP^2+4*Driver.innerP^2*(2*Driver.heightP+1)+2
noncomputable def componentP : Polynomial ℕ := termP+2
noncomputable def accumulatorP : Polynomial ℕ := 1+(termP+1)*Driver.countP+termP+2
noncomputable def answerP : Polynomial ℕ := (vertexP+1)^2+2
noncomputable def queryInputP : Polynomial ℕ := X+Driver.degreeP+Driver.innerP+answerP
noncomputable def normInputP : Polynomial ℕ := Driver.innerP+Driver.heightP+X
noncomputable def ratioTime : Polynomial ℕ :=
  GridWeightsRuntime.pairTime.comp Driver.degreeP+EvenWeightsRuntime.time.comp Driver.innerP+
  OddFactorialNormalization.time.comp normInputP+5*answerP+RatioCombine.time.comp componentP+10
noncomputable def cellTime (P : Polynomial ℕ) : Polynomial ℕ :=
  P.comp queryInputP+ratioTime+AccumulatorInto.time.comp accumulatorP+answerP+7

@[simp] lemma vertexP_eval (L : ℕ) : vertexP.eval L=CliqueRecovery.vertexBound L := by simp [vertexP,CliqueRecovery.vertexBound]
@[simp] lemma termP_eval (L : ℕ) : termP.eval L=CliqueRecovery.termExponent L := by simp [termP,CliqueRecovery.termExponent]
@[simp] lemma componentP_eval (L : ℕ) : componentP.eval L=CliqueRecovery.termExponent L+2 := by simp [componentP]
@[simp] lemma accumulatorP_eval (L : ℕ) : accumulatorP.eval L=
    1+(CliqueRecovery.termExponent L+1)*Recovery.queryCountBound L+CliqueRecovery.termExponent L+2 := by simp [accumulatorP]

lemma actual_cellBound (P : Polynomial ℕ) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (mode : Bool) (w : WordInstance) (hw : w.word≠[]) (q : Recovery.Index w)
    (hg : answerValue g bytes w q=perfectMatchingCount (CliqueRecovery.query mode w q).2.graph) :
    cellBound P g bytes w q (componentP.eval (wordBits w).length) (accumulatorP.eval (wordBits w).length)≤
      (cellTime P).eval (wordBits w).length := by
  let L := (wordBits w).length
  have hp : w.particles≤L := by have := wordBits_length_lower w;dsimp [L];omega
  have hd : Recovery.degree w≤Driver.degreeP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).1
  have hh : Recovery.height w q.1≤Driver.heightP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).2.1
  have he : Recovery.innerDegree w q.1≤Driver.innerP.eval L := by simpa [L] using (Recovery.parameter_bounds w q.1).2.2
  have ht : q.1.val≤Driver.degreeP.eval L := by have := q.1.isLt;omega
  have hs : q.2.val≤Driver.innerP.eval L := by have := q.2.isLt;omega
  have hA : (signedBits (answerValue g bytes w q:ℤ)).length≤answerP.eval L := by
    rw [hg]
    have hb : (perfectMatchingCount (CliqueRecovery.query mode w q).2.graph:ℤ).natAbs≤2^((CliqueRecovery.vertexBound L+1)^2) :=
      CliqueRecovery.query_answer_bound mode w hw q
    have h := signedBits_length_of_abs_bound hb
    simpa only [answerP,eval_add,eval_pow,eval_one,eval_ofNat,vertexP_eval] using h
  have hQ : L+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length≤queryInputP.eval L := by
    simp only [queryInputP,eval_add,eval_X]
    omega
  have hN : q.2.val+Recovery.height w q.1+w.particles≤normInputP.eval L := by
    simp only [normInputP,eval_add,eval_X]
    omega
  have hqtime := polynomial_nat_eval_mono P hQ
  have hotime := polynomial_nat_eval_mono GridWeightsRuntime.pairTime hd
  have hitime := polynomial_nat_eval_mono EvenWeightsRuntime.time he
  have hntime := polynomial_nat_eval_mono OddFactorialNormalization.time hN
  dsimp only at hqtime hotime hitime hntime
  unfold cellBound CliqueRatioCell.costBound
  simp only [cellTime,ratioTime,eval_add,eval_mul,eval_comp,eval_ofNat]
  change P.eval (L+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length)+
    (GridWeightsRuntime.pairTime.eval (Recovery.degree w)+EvenWeightsRuntime.time.eval (Recovery.innerDegree w q.1)+
      OddFactorialNormalization.time.eval (q.2.val+Recovery.height w q.1+w.particles)+
      5*(signedBits (answerValue g bytes w q:ℤ)).length+RatioCombine.time.eval (componentP.eval L)+10)+
      AccumulatorInto.time.eval (accumulatorP.eval L)+(signedBits (answerValue g bytes w q:ℤ)).length+7≤_
  dsimp only [L] at *
  omega
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver
