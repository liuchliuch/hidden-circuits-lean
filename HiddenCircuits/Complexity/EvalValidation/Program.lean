import HiddenCircuits.Complexity.EvalValidation.Finish
import HiddenCircuits.Complexity.EvalValidation.SemanticsSoundness

/-! Actual finite polynomial raw-byte validation for both standalone problems.
The input is preserved, acceptance is [true] on port1, rejection is empty,
and every other work register is cleared. -/
namespace HiddenCircuits.Complexity.EvalValidation.Program
open OracleBlock Polynomial
set_option maxHeartbeats 900000
noncomputable def program (pairMode : Bool) : OracleBlock 31 := seq (Prepare.run pairMode) Finish.program
noncomputable def runTime : Polynomial ℕ := 200000*(X+1)^2
noncomputable def time : Polynomial ℕ := runTime+300*(X+runTime+1)+2

theorem program_executes (g : BitString→ℕ) (pairMode : Bool) (xs : BitString) :
    ∃c,(program pairMode).Executes g (Function.update (fun _=>[]) 0 xs)
      (Finish.output xs (Semantics.test pairMode xs)) c ∧ c≤time.eval xs.length := by
  obtain ⟨a,ha,hab⟩:=Prepare.run_executes g pairMode xs
  have hin:∀i : Fin 32,((Function.update (fun _=>[]) 0 xs : Store 31) i).length≤xs.length := by
    intro i
    by_cases hi:i=0
    · subst i;simp
    · simp [Function.update_of_ne hi]
  have hs:∀i : Fin 32,(Prepare.finished pairMode xs i).length≤xs.length+a:=ha.stack_bound hin
  obtain ⟨b,hb,hbb⟩:=Finish.program_executes g xs [] (Semantics.header xs) (Semantics.width xs)
    (Semantics.runFlags pairMode (Semantics.width xs) (Semantics.second xs).right (Semantics.beforeFlags pairMode xs))
    (xs.length+a) hs
  rw [Semantics.runFlags_all] at hb
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [time,runTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  omega

theorem pair_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,(program true).Executes g (Function.update (fun _=>[]) 0 xs)
      (Finish.output xs (decodePairInput xs).isSome) c ∧ c≤time.eval xs.length := by
  simpa only [Semantics.test_pair_decode] using program_executes g true xs

theorem word_executes (g : BitString→ℕ) (xs : BitString) :
    ∃c,(program false).Executes g (Function.update (fun _=>[]) 0 xs)
      (Finish.output xs (decodeWord xs).isSome) c ∧ c≤time.eval xs.length := by
  simpa only [Semantics.test_word_decode] using program_executes g false xs
end HiddenCircuits.Complexity.EvalValidation.Program
