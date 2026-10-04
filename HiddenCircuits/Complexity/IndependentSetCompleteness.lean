import HiddenCircuits.Complexity.SourceGrid.Program
import HiddenCircuits.Complexity.CNFCloneEmitter.Runtime

/-! Unconditional machine-grounded #P-completeness of ordinary all-independent-
set counting on actual canonical binary graph inputs. The source reduction
instantiates every operational emitter, grid loop and integer arithmetic stage. -/
namespace HiddenCircuits.Complexity
open OracleBlock

namespace IndependentSetReduction

/-- The actual fixed forty-three-stack canonical-CNF oracle solver. -/
noncomputable def program : OracleBlock 42 := SourceGrid.program CNFCloneEmitter.program
noncomputable def time : Polynomial ℕ := SourceGrid.time CNFCloneEmitter.timeBound

/-- The sole final component is supplied by its concrete bit-instruction proof. -/
theorem cloneEmitter_executes (F : CNFInput) (a b : ℕ) :
    ∃ c, CNFCloneEmitter.program.Executes GraphInput.independentSetProblem
      (SourceGrid.queryStore (CNFInput.encode F) a b [])
      (SourceGrid.queryStore (CNFInput.encode F) a b (F.2.2.encodedCloneQuery a b)) c ∧
      c≤CNFCloneEmitter.timeBound.eval ((CNFInput.encode F).length+a+b) :=
  CNFCloneEmitter.program_executes GraphInput.independentSetProblem F.2.2 a b

/-- Exact canonical-CNF counting using only ordinary all-independent-set graph
queries. No arithmetic, encoding, source hardness or time premise remains. -/
theorem program_executes (F : CNFInput) :
    ∃ s : Store 42, ∃ c, program.Executes GraphInput.independentSetProblem
      (Function.update (fun _ => []) 0 (CNFInput.encode F)) s c ∧
      s 0=Computability.encodeNat F.2.2.satCount ∧ c≤time.eval (CNFInput.encode F).length :=
  SourceGrid.program_executes CNFCloneEmitter.program CNFCloneEmitter.timeBound cloneEmitter_executes F

end IndependentSetReduction

/-- Genuine source hardness from arbitrary mathlib polynomial-time verifier
machines, via the parsimonious Cook compiler and the fully executed clone grid. -/
theorem independentSet_sharpPHard : SharpPHard GraphInput.independentSetProblem :=
  SourceGrid.independentSet_hard_of_clone_emitter CNFCloneEmitter.program CNFCloneEmitter.timeBound
    IndependentSetReduction.cloneEmitter_executes

theorem SharpP.reduces_to_independentSet {f : BitString → ℕ} (hf : SharpP f) :
    PolyTuringReduction f GraphInput.independentSetProblem := independentSet_sharpPHard f hf

/-- Both membership and hardness refer to actual finite programs, exact binary
encodings and charged bit-operation runtimes. This counts all independent sets. -/
theorem independentSet_sharpPComplete : SharpPComplete GraphInput.independentSetProblem :=
  ⟨GraphVerifier.Runtime.independentSet_sharpP,independentSet_sharpPHard⟩

end HiddenCircuits.Complexity
