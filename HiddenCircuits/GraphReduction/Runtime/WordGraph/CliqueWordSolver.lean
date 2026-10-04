import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriverPolynomial
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueQueryAnswer

/-! Concrete clean signed word solvers for the runtime-supported clique targets.
Every model hypothesis is discharged by the actual query and arithmetic blocks. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 700000

noncomputable def term (mode : Bool) (w : WordInstance) (q : Recovery.Index w) : ℤ×ℤ :=
  CliqueRecovery.ratio mode w q (perfectMatchingCount (CliqueRecovery.query mode w q).2.graph)

lemma initialBitBound (mode : Bool) (w : WordInstance) (hw : w.word≠[]) :
    RationalAccumulator.BitBound (accumulatorP.eval (wordBits w).length) (0,1)
      (GenericDriver.terms w (term mode w)) := by
  have h := RationalAccumulator.bitBound_of_abs (0,1) (GenericDriver.terms w (term mode w)) 1
    (CliqueRecovery.termExponent (wordBits w).length) (by constructor <;> decide) (by
      intro b hb
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
      exact CliqueRecovery.ratio_bound mode w hw q)
  apply h.mono
  rw [accumulatorP_eval]
  have hl : (GenericDriver.terms w (term mode w)).length≤Recovery.queryCountBound (wordBits w).length := by
    simpa only [GenericDriver.terms,Recovery.terms,List.length_map] using Recovery.terms_length_bound w
  nlinarith

lemma modelSpec (Q : OracleBlock 85) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (P : Polynomial ℕ) (hQ : QuerySpec Q g bytes P) (mode : Bool) (w : WordInstance)
    (hw : w.word≠[]) (hg : CorrectOracle g bytes mode w) :
    GenericDriver.ModelSpec (cell Q mode) g w (term mode w) accumulatorP (cellTime P) := by
  refine ⟨?_,initialBitBound mode w hw,?_,CliqueRecovery.terms_value mode w hw⟩
  · intro q a hA hR
    have hC : CliqueRatioCell.componentBound mode w q (answerValue g bytes w q)
        (componentP.eval (wordBits w).length) := by
      unfold CliqueRatioCell.componentBound
      rw [hg q,componentP_eval]
      exact CliqueRecovery.ratio_registers_bounded mode w hw q
    have hR' : (signedBits (CliqueRecovery.ratio mode w q (answerValue g bytes w q)).1).length≤accumulatorP.eval (wordBits w).length ∧
        (signedBits (CliqueRecovery.ratio mode w q (answerValue g bytes w q)).2).length≤accumulatorP.eval (wordBits w).length := by
      rw [hg q]
      exact hR
    obtain ⟨c,hc,hb⟩ := cell_executes Q g bytes P hQ mode w q a
      (componentP.eval (wordBits w).length) (accumulatorP.eval (wordBits w).length) hC hA hR'
    rw [hg q] at hc
    exact ⟨c,hc,hb.trans (actual_cellBound P g bytes mode w hw q (hg q))⟩
  · intro q
    exact CliqueRecovery.ratio_nonzero _ _ _ _

noncomputable def program (kind : CliqueWordQuery.Kind) : OracleBlock 97 :=
  GenericDriver.program (cell (CliqueQueryAnswer.program kind) (CliqueWordQuery.mode kind))
noncomputable def time (kind : CliqueWordQuery.Kind) : Polynomial ℕ :=
  GenericDriver.time accumulatorP (cellTime (CliqueQueryAnswer.time kind))

/-- The program accepts only canonical word bits, leaves only canonical signed
answer bits, and has a closed input-length polynomial operational cost. -/
theorem program_executes (kind : CliqueWordQuery.Kind) (g : BitString → ℕ) (w : WordInstance)
    (hg : w.word≠[]→CorrectOracle g (CliqueWordQuery.queryBits kind) (CliqueWordQuery.mode kind) w) :
    ∃z : ℤ, ∃c, (program kind).Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧
      c≤(time kind).eval (wordBits w).length := by
  apply GenericDriver.program_executes (cell (CliqueQueryAnswer.program kind) (CliqueWordQuery.mode kind)) g w
    (term (CliqueWordQuery.mode kind) w) accumulatorP (cellTime (CliqueQueryAnswer.time kind))
  intro hw
  exact modelSpec (CliqueQueryAnswer.program kind) g (CliqueWordQuery.queryBits kind) (CliqueQueryAnswer.time kind)
    (CliqueQueryAnswer.program_polynomial kind g) (CliqueWordQuery.mode kind) w hw (hg hw)

end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver
