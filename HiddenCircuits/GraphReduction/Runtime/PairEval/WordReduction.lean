import HiddenCircuits.Complexity.EvalValidation.Program
import HiddenCircuits.GraphReduction.Runtime.PairEval.WordRawGuard

/-! Lemma3.3 as a genuine all-raw polynomial Turing reduction between the
already defined standalone total functions, including malformed-byte rejection. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.WordReduction
open Complexity OracleBlock Polynomial
open Circuit.Runtime

lemma validatorSpec : WordRawGuard.ValidatorSpec (EvalValidation.Program.program false) EvalValidation.Program.time := by
  intro g xs
  obtain ⟨c,hc,hb⟩:=EvalValidation.Program.word_executes g xs
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> simp [EvalValidation.Finish.output,WordRawGuard.validationStore,WordRawGuard.marker]
noncomputable def program : OracleBlock 128 := WordRawGuard.program (EvalValidation.Program.program false)
noncomputable def time : Polynomial ℕ := WordRawGuard.time EvalValidation.Program.time

theorem program_executes (g : BitString→ℕ) (hg : WordCell.oracleSpec g) (xs : BitString) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (WordEvalOracle.problem xs))) c ∧ c≤time.eval xs.length :=
  WordRawGuard.program_executes _ _ validatorSpec g hg xs

theorem reduction_of_oracle (g : BitString→ℕ) (hg : WordCell.oracleSpec g) :
    PolyTuringReduction WordEvalOracle.problem g := WordRawGuard.reduction _ _ validatorSpec g hg

theorem wordEval_le_pairEval : PolyTuringReduction WordEvalOracle.problem pairEval :=
  reduction_of_oracle pairEval WordCell.problem_spec
end HiddenCircuits.GraphReduction.Runtime.PairEval.WordReduction
