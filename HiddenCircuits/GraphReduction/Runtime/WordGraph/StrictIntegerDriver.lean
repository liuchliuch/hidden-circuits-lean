import HiddenCircuits.GraphReduction.Runtime.WordGraph.StrictIntegerAnswer
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WideSolver
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueWordSolver

/-! The concrete wider unit-interval representation query and arithmetic cell. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.StrictIntegerDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
open CliqueDriver (answerValue CorrectOracle cellBound)
set_option maxHeartbeats 1800000

def queryEmbedding : Fin 124 ↪ Fin 136 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 6 else if i.val=2 then 9 else if i.val=3 then 12 else ⟨i.val+12,by omega⟩
  inj' := by decide +kernel
noncomputable def queryCell : OracleBlock 135 := rename StrictIntegerAnswer.program queryEmbedding
noncomputable def cell : OracleBlock 135 := seq queryCell
  (seq (WideDriver.lift 38 (CliqueDriver.ratioCell false))
    (seq (WideDriver.lift 38 Driver.accumulate) (WideDriver.lift 38 (clear 12))))

lemma queryCell_executes (g : BitString → ℕ) (w : WordInstance) (q : Recovery.Index w) (a : ℤ×ℤ) :
    ∃c, queryCell.Executes g
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answerValue g StrictIntegerAnswer.queryBits w q:ℤ)) [] []) c ∧
      c≤StrictIntegerAnswer.time.eval ((wordBits w).length+q.1.val+q.2.val+(signedBits (answerValue g StrictIntegerAnswer.queryBits w q:ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := StrictIntegerAnswer.program_polynomial g w q.1.val q.2.val
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ queryEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · clear hc hb
    intro i hi
    have h12 : i.val≠12 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [WideDriver.state,WideDriver.extend,Driver.state,h12,if_false]

theorem cell_executes (g : BitString → ℕ) (w : WordInstance) (q : Recovery.Index w)
    (a : ℤ×ℤ) (BC BA : ℕ) (hC : CliqueRatioCell.componentBound false w q (answerValue g StrictIntegerAnswer.queryBits w q) BC)
    (hA : (signedBits a.1).length≤BA ∧ (signedBits a.2).length≤BA)
    (hR : (signedBits (CliqueRecovery.ratio false w q (answerValue g StrictIntegerAnswer.queryBits w q)).1).length≤BA ∧
      (signedBits (CliqueRecovery.ratio false w q (answerValue g StrictIntegerAnswer.queryBits w q)).2).length≤BA) :
    ∃c, cell.Executes g
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio false w q (answerValue g StrictIntegerAnswer.queryBits w q))) [] [] []) c ∧
      c≤cellBound StrictIntegerAnswer.time g StrictIntegerAnswer.queryBits w q BC BA := by
  obtain ⟨c,hc,hcb⟩ := queryCell_executes g w q a
  obtain ⟨d,hd,hdb⟩ := CliqueDriver.ratioCell_executes g false w q a (answerValue g StrictIntegerAnswer.queryBits w q) BC hC
  obtain ⟨e,he,heb⟩ := Driver.accumulate_executes g w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1)
    (Recovery.innerDegree w q.1-q.2.val) q.2.val a (CliqueRecovery.ratio false w q (answerValue g StrictIntegerAnswer.queryBits w q))
    (signedBits (answerValue g StrictIntegerAnswer.queryBits w q:ℤ)) BA hA hR
  have hz : (clear (12:Fin 98)).Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio false w q (answerValue g StrictIntegerAnswer.queryBits w q))) (signedBits (answerValue g StrictIntegerAnswer.queryBits w q:ℤ)) [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio false w q (answerValue g StrictIntegerAnswer.queryBits w q))) [] [] [])
      ((signedBits (answerValue g StrictIntegerAnswer.queryBits w q:ℤ)).length+1) := by
    convert clear_executes g (12:Fin 98)
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio false w q (answerValue g StrictIntegerAnswer.queryBits w q))) (signedBits (answerValue g StrictIntegerAnswer.queryBits w q:ℤ)) [] []) using 1
    clear hc hd he hcb hdb heb
    funext i;fin_cases i <;> rfl
  have hdWide := WideDriver.lift_executes 38 (CliqueDriver.ratioCell false) g _ _ _ hd
  have heWide := WideDriver.lift_executes 38 Driver.accumulate g _ _ _ he
  have hzWide := WideDriver.lift_executes 38 (clear 12) g _ _ _ hz
  exact ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hdWide (seq_executes _ _ g heWide hzWide)),by unfold cellBound;omega⟩
end HiddenCircuits.GraphReduction.Runtime.WordGraph.StrictIntegerDriver
