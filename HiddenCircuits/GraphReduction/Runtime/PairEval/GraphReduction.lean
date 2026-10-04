import HiddenCircuits.Complexity.EvalValidation.Program
import HiddenCircuits.GraphReduction.Runtime.PairEval.RawGuard

/-! Standalone all-raw PairEval reductions. Malformed source bytes return zero
through the concrete finite validator. Every target query is physically built
and every validation/interpolation/answer bit is charged. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Reduction
open Complexity OracleBlock Polynomial

lemma validatorSpec : RawGuard.ValidatorSpec (EvalValidation.Program.program true) EvalValidation.Program.time := by
  intro g xs
  obtain ⟨c,hc,hb⟩:=EvalValidation.Program.pair_executes g xs
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> simp [EvalValidation.Finish.output,RawGuard.validationStore,RawGuard.marker]
noncomputable def program (kind : Driver.Target) : OracleBlock 128 := RawGuard.program (EvalValidation.Program.program true) kind
noncomputable def time (kind : Driver.Target) : Polynomial ℕ := RawGuard.time EvalValidation.Program.time kind

theorem program_executes (kind : Driver.Target) (g : BitString→ℕ) (hg : ∀w,Driver.CorrectOracle kind g w) (xs : BitString) :
    ∃c,(program kind).Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (pairEval xs))) c ∧ c≤(time kind).eval xs.length :=
  RawGuard.program_executes _ _ validatorSpec kind g hg xs

theorem reduction_of_oracle (kind : Driver.Target) (g : BitString→ℕ) (hg : ∀w,Driver.CorrectOracle kind g w) :
    PolyTuringReduction pairEval g := RawGuard.reduction _ _ validatorSpec kind g hg

theorem pairEval_to_monotone (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>MonotoneGraph G.2.graph) g) :
    PolyTuringReduction pairEval g := reduction_of_oracle none g (GraphSolver.monotone_correct g hg)
/-- Proposition10.1 for the original malformed-zero PairEval function. The
sample graphs are all unit interval and use actual nonnegative even probes. -/
theorem pairEval_to_unitInterval (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>UnitIntervalGraph G.2.graph) g) :
    PolyTuringReduction pairEval g := reduction_of_oracle (some .unit) g (GraphSolver.unit_correct g hg)
theorem pairEval_to_chordalPermutation (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>ChordalPermutationGraph G.2.graph) g) :
    PolyTuringReduction pairEval g := reduction_of_oracle (some .privateGraph) g (GraphSolver.private_correct g hg)
theorem pairEval_to_suppliedChordalPermutation (g : BitString→ℕ) (hg : SuppliedChordalPermutationOracle g) :
    PolyTuringReduction pairEval g := reduction_of_oracle (some .suppliedPrivate) g (GraphSolver.suppliedPrivate_correct g hg)

theorem canonical_graph_reduction (kind : Driver.Target) (hk : kind≠some .suppliedPrivate) :
    PolyTuringReduction pairEval GraphInput.perfectMatchingProblem := by
  apply reduction_of_oracle kind GraphInput.perfectMatchingProblem
  intro w s
  cases kind with
  | none => exact GraphPromises.canonical_spec none w s
  | some k => cases k with
    | unit => exact GraphPromises.canonical_spec (some false) w s
    | privateGraph => exact GraphPromises.canonical_spec (some true) w s
    | suppliedPrivate => exact (hk rfl).elim
theorem canonical_supplied_reduction : PolyTuringReduction pairEval GraphPromises.suppliedPrivateProblem :=
  reduction_of_oracle (some .suppliedPrivate) GraphPromises.suppliedPrivateProblem GraphPromises.suppliedPrivate_canonical
end HiddenCircuits.GraphReduction.Runtime.PairEval.Reduction
