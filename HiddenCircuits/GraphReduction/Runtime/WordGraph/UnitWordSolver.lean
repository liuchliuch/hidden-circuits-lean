import HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitDriver

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
open CliqueDriver (CorrectOracle answerValue accumulatorP componentP cellTime term initialBitBound actual_cellBound componentP_eval)

noncomputable def program : OracleBlock 135 := WideDriver.program cell
noncomputable def time : Polynomial ℕ := GenericDriver.time accumulatorP (cellTime UnitQueryAnswer.time)

lemma modelSpec (g : BitString → ℕ) (w : WordInstance) (hw : w.word≠[])
    (hg : CorrectOracle g UnitQueryAnswer.queryBits false w) :
    WideDriver.ModelSpec cell g w (term false w) accumulatorP (cellTime UnitQueryAnswer.time) := by
  refine ⟨?_,initialBitBound false w hw,?_,CliqueRecovery.terms_value false w hw⟩
  · intro q a hA hR
    have hC : CliqueRatioCell.componentBound false w q (answerValue g UnitQueryAnswer.queryBits w q)
        (componentP.eval (wordBits w).length) := by
      unfold CliqueRatioCell.componentBound
      rw [hg q,componentP_eval]
      exact CliqueRecovery.ratio_registers_bounded false w hw q
    have hR' : (signedBits (CliqueRecovery.ratio false w q (answerValue g UnitQueryAnswer.queryBits w q)).1).length≤accumulatorP.eval (wordBits w).length ∧
        (signedBits (CliqueRecovery.ratio false w q (answerValue g UnitQueryAnswer.queryBits w q)).2).length≤accumulatorP.eval (wordBits w).length := by
      rw [hg q]
      exact hR
    obtain ⟨c,hc,hb⟩ := cell_executes g w q a
      (componentP.eval (wordBits w).length) (accumulatorP.eval (wordBits w).length) hC hA hR'
    rw [hg q] at hc
    exact ⟨c,hc,hb.trans (actual_cellBound UnitQueryAnswer.time g UnitQueryAnswer.queryBits false w hw q (hg q))⟩
  · intro q
    exact CliqueRecovery.ratio_nonzero _ _ _ _

theorem program_executes (g : BitString → ℕ) (w : WordInstance)
    (hg : w.word≠[]→CorrectOracle g UnitQueryAnswer.queryBits false w) :
    ∃z : ℤ, ∃c, program.Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧
      c≤time.eval (wordBits w).length := by
  apply WideDriver.program_executes cell g w (term false w) accumulatorP (cellTime UnitQueryAnswer.time)
  intro hw
  exact modelSpec g w hw (hg hw)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.UnitDriver
