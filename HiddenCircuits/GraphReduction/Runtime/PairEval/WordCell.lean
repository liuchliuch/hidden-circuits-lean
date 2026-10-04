import HiddenCircuits.GraphReduction.Runtime.PairEval.WordQuery
import HiddenCircuits.GraphReduction.Runtime.PairEval.WordRecovery
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver

namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordCell
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
set_option maxHeartbeats 1200000

def oracleSpec (g : BitString→ℕ) : Prop := ∀w : PairInput,g (pairInputBits w)=w.value
lemma problem_spec : oracleSpec pairEval := by intro w;exact pairEval_pairInputBits w
lemma sampled_answer (g : BitString→ℕ) (hg : oracleSpec g) (w : WordInstance) (hw : w.word≠[]) (t : ℕ) :
    g (WordQuery.queryBits w t)=WordRecovery.answer w t := hg (WordQuery.sampleInput w hw t)
noncomputable def queryCell : OracleBlock 97 := rename WordQuery.program Driver.queryEmbedding
noncomputable def ratioCell : OracleBlock 97 := rename WordRatio.program Driver.ratioEmbedding
noncomputable def active : OracleBlock 97 := seq queryCell (seq ratioCell (seq Driver.accumulate (clear 12)))
noncomputable def program : OracleBlock 97 := branchPop 9 active (push 9 false) (push 9 true)
noncomputable def queryInputP : Polynomial ℕ := X+Driver.degreeP+Driver.innerP+Driver.answerP
noncomputable def time : Polynomial ℕ := WordQuery.time.comp queryInputP+
  GridWeightsRuntime.pairTime.comp Driver.degreeP+6*Driver.answerP+RatioCombine.time.comp Driver.componentP+
  AccumulatorInto.time.comp Driver.accumulatorP+51

lemma ratio_executes (g : BitString→ℕ) (w : WordInstance) (q : Recovery.Index w) (a : ℤ×ℤ) (answer B : ℕ)
    (hB : RegisterMachine.Bounded B (RatioCombine.registers 1 (answer:ℤ)
      (interpolationNegativeNumerator (Recovery.degree w) q.1) 1 (interpolationDenominator (Recovery.degree w) q.1) 1 1)) :
    ∃c,ratioCell.Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a (signedBits (answer:ℤ)) [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a (signedBits (answer:ℤ))
        (signedBits (WordRatio.ratio (Recovery.degree w) q.1 answer).1) (signedBits (WordRatio.ratio (Recovery.degree w) q.1 answer).2)) c ∧
      c≤WordRatio.time (Recovery.degree w) answer B := by
  obtain ⟨c,hc,hb⟩:=WordRatio.program_executes g (Recovery.degree w) q.1 q.2.val (Recovery.innerDegree w q.1-q.2.val)
    w.particles (Recovery.height w q.1) answer B hB
  refine ⟨c,?_,hb⟩
  apply rename_executes_to WordRatio.program Driver.ratioEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h13:i.val≠13:=by intro h;exact hi 7 (Fin.ext h.symm)
    have h14:i.val≠14:=by intro h;exact hi 8 (Fin.ext h.symm)
    simp only [Driver.state,h13,h14,if_false]

lemma active_executes (g : BitString→ℕ) (hg : oracleSpec g) (w : WordInstance) (hw : w.word≠[])
    (q : Recovery.Index w) (a : ℤ×ℤ)
    (hA : (signedBits a.1).length≤Driver.accumulatorP.eval (wordBits w).length ∧ (signedBits a.2).length≤Driver.accumulatorP.eval (wordBits w).length)
    (hR : (signedBits (WordRatio.ratio (Recovery.degree w) q.1 (WordRecovery.answer w q.1.val)).1).length≤Driver.accumulatorP.eval (wordBits w).length ∧
      (signedBits (WordRatio.ratio (Recovery.degree w) q.1 (WordRecovery.answer w q.1.val)).2).length≤Driver.accumulatorP.eval (wordBits w).length) :
    ∃c,active.Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (WordRatio.ratio (Recovery.degree w) q.1 (WordRecovery.answer w q.1.val))) [] [] []) c ∧
      c+2≤time.eval (wordBits w).length := by
  let ans:=WordRecovery.answer w q.1.val
  let rat:=WordRatio.ratio (Recovery.degree w) q.1 ans
  have hQ:CliqueDriver.QuerySpec WordQuery.program g (fun w t _=>WordQuery.queryBits w t) WordQuery.time :=
    WordQuery.program_polynomial g
  obtain ⟨c,hc,hcb⟩:=CliqueDriver.queryCell_executes WordQuery.program g (fun w t _=>WordQuery.queryBits w t) WordQuery.time hQ w q a
  have hAns:=sampled_answer g hg w hw q.1.val
  change g (WordQuery.queryBits w q.1.val)=ans at hAns
  simp only [CliqueDriver.answerValue,hAns] at hc hcb
  obtain ⟨d,hd,hdb⟩:=ratio_executes g w q a ans (Driver.componentP.eval (wordBits w).length) (WordRecovery.registers_bounded w hw q.1)
  obtain ⟨e,he,heb⟩:=Driver.accumulate_executes g w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1)
    (Recovery.innerDegree w q.1-q.2.val) q.2.val a rat (signedBits (ans:ℤ))
    (Driver.accumulatorP.eval (wordBits w).length) hA hR
  have hz:(clear (12:Fin 98)).Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a rat) (signedBits (ans:ℤ)) [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a rat) [] [] []) ((signedBits (ans:ℤ)).length+1) := by
    convert clear_executes g (12:Fin 98) (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1)
      (Recovery.innerDegree w q.1-q.2.val) q.2.val (RationalAccumulator.step a rat) (signedBits (ans:ℤ)) [] []) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hd (seq_executes _ _ g he hz)),?_⟩
  let L:=(wordBits w).length
  have hdB:Recovery.degree w≤Driver.degreeP.eval L:=by simpa [L] using (Recovery.parameter_bounds w q.1).1
  have hsB:Recovery.innerDegree w q.1≤Driver.innerP.eval L:=by simpa [L] using (Recovery.parameter_bounds w q.1).2.2
  have ht:q.1.val≤Driver.degreeP.eval L:=by have := q.1.isLt;omega
  have hs:q.2.val≤Driver.innerP.eval L:=by have := q.2.isLt;omega
  have hbits:(signedBits (ans:ℤ)).length≤Driver.answerP.eval L := by
    have h:=signedBits_length_of_abs_bound (WordRecovery.answer_bound w hw q.1)
    simpa [Driver.answerP,L] using h
  have hinput:L+q.1.val+q.2.val+(signedBits (ans:ℤ)).length≤queryInputP.eval L := by
    simp only [queryInputP,eval_add,eval_X];omega
  have hqt:=polynomial_nat_eval_mono WordQuery.time hinput
  have hwt:=polynomial_nat_eval_mono GridWeightsRuntime.pairTime hdB
  dsimp only at hqt hwt
  unfold WordRatio.time at hdb
  simp only [time,eval_add,eval_mul,eval_comp,eval_ofNat]
  dsimp only [L] at *
  omega

lemma program_spec (g : BitString→ℕ) (hg : oracleSpec g) (w : WordInstance) (hw : w.word≠[]) :
    GenericDriver.CellSpec program g w (WordRecovery.term w) (Driver.accumulatorP.eval (wordBits w).length) (time.eval (wordBits w).length) := by
  intro q a hA hR
  by_cases hz:q.2.val=0
  · simp only [WordRecovery.term,hz,if_pos] at hR ⊢
    obtain ⟨c,hc,hb⟩:=active_executes g hg w hw q a hA hR
    rw [hz] at hc
    refine ⟨c+2,branchPop_empty 9 active (push 9 false) (push 9 true) g ?_ hc,hb⟩
    simp [Driver.state,hz]
  · have hs:0<q.2.val:=by omega
    have hn:q.2.val=(q.2.val-1)+1:=by omega
    let st:=Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1)
      (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] []
    have h9:st 9=true::List.replicate (q.2.val-1) true := by
      change List.replicate q.2.val true=_
      conv_lhs => rw [hn,List.replicate_succ]
    have hp:(push (9:Fin 98) true).Executes g (Function.update st 9 (List.replicate (q.2.val-1) true)) st 1 := by
      convert push_executes g (9:Fin 98) true (Function.update st 9 (List.replicate (q.2.val-1) true)) using 1
      rw [Function.update_self,Function.update_idem,←h9,Function.update_eq_self]
    have he:=branchPop_true (9:Fin 98) active (push 9 false) (push 9 true) g h9 hp
    refine ⟨3,?_,?_⟩
    · simpa [WordRecovery.term,hz,RationalAccumulator.step,st] using he
    · simp only [time,eval_add,eval_mul,eval_comp,eval_ofNat]
      omega
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordCell
