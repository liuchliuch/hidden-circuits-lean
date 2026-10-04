import HiddenCircuits.Circuit.Runtime.DeltaWordDriver
import HiddenCircuits.Circuit.Runtime.WordEvalHardness
import HiddenCircuits.Complexity.NativeValidation.Guard

/-! Independent Lemma 7.1 as an all-raw polynomial Turing reduction of the
original native rational-coded Delta problem, including malformed-zero inputs. -/
namespace HiddenCircuits.Circuit.Runtime.DeltaRawReduction
open Complexity OracleBlock Polynomial
noncomputable def program : OracleBlock 96 := NativeValidation.Guard.deltaProgram DeltaWordEvaluation.program
noncomputable def time : Polynomial ℕ := NativeValidation.Guard.time DeltaWordEvaluation.time
lemma solverSpec (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) :
    RawValidationGuard.SolverSpec NativeValidation.Guard.deltaInput DeltaWordEvaluation.program DeltaWordEvaluation.time g :=
  DeltaWordEvaluation.native_executes g hg

theorem program_executes (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) (xs : BitString) :
    ∃c,program.Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (deltaProblem xs))) c ∧ c≤time.eval xs.length :=
  NativeValidation.Guard.delta_executes _ _ g (solverSpec g hg) xs

theorem reduction_of_oracle (g : BitString→ℕ) (hg : WordEvalOracle.oracleSpec g) :
    PolyTuringReduction deltaProblem g := NativeValidation.Guard.delta_reduction _ _ g (solverSpec g hg)

theorem deltaEval_le_wordEval : PolyTuringReduction deltaProblem WordEvalOracle.problem :=
  reduction_of_oracle WordEvalOracle.problem WordEvalOracle.problem_spec
end HiddenCircuits.Circuit.Runtime.DeltaRawReduction
