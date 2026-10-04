import HiddenCircuits.Complexity.NativeValidation.SemanticsSoundness
import HiddenCircuits.Complexity.NativeValidation.Prepare
import HiddenCircuits.Complexity.EvalValidation.Finish

/-! Real finite native-circuit input validation. Header zero is allowed; gate
placements determine whether any nonempty gate list is possible. -/
namespace HiddenCircuits.Complexity.NativeValidation.Program
open OracleBlock Polynomial
set_option maxHeartbeats 900000
noncomputable def program (deltaMode : Bool) : OracleBlock 31 := seq (Prepare.run deltaMode) EvalValidation.Finish.program
noncomputable def runTime : Polynomial ℕ := 100000*(X+1)^2
noncomputable def time : Polynomial ℕ := runTime+300*(X+runTime+1)+2

theorem program_executes (g : BitString→ℕ) (deltaMode : Bool) (xs : BitString) :
    ∃c,(program deltaMode).Executes g (Function.update (fun _=>[]) 0 xs)
      (EvalValidation.Finish.output xs (Semantics.test deltaMode xs)) c ∧ c≤time.eval xs.length := by
  obtain ⟨a,ha,hab⟩:=Prepare.run_executes g deltaMode xs
  have hin:∀i : Fin 32,((Function.update (fun _=>[]) 0 xs : Store 31) i).length≤xs.length := by
    intro i
    by_cases hi:i=0
    · subst i;simp
    · simp [Function.update_of_ne hi]
  have hs:∀i : Fin 32,(Prepare.finished deltaMode xs i).length≤xs.length+a:=ha.stack_bound hin
  obtain ⟨b,hb,hbb⟩:=EvalValidation.Finish.program_executes g xs [] [] (Semantics.header xs)
    (Semantics.runFlags deltaMode (Semantics.header xs) (Semantics.payload xs) (Semantics.flags xs))
    (xs.length+a) hs
  rw [Semantics.runFlags_all] at hb
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [time,runTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  omega

theorem constraint_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,(program false).Executes g (Function.update (fun _=>[]) 0 xs)
      (EvalValidation.Finish.output xs (ConstraintInput.decode xs).isSome) c ∧ c≤time.eval xs.length := by
  simpa only [Semantics.test_constraint_decode] using program_executes g false xs
theorem delta_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,(program true).Executes g (Function.update (fun _=>[]) 0 xs)
      (EvalValidation.Finish.output xs (DeltaInput.decode xs).isSome) c ∧ c≤time.eval xs.length := by
  simpa only [Semantics.test_delta_decode] using program_executes g true xs

end HiddenCircuits.Complexity.NativeValidation.Program
