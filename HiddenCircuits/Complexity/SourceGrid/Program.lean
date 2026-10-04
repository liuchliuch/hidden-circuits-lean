import HiddenCircuits.Complexity.SourceGrid.Setup
import HiddenCircuits.Complexity.SourceGrid.Loop
import HiddenCircuits.Complexity.SourceGrid.Finish
import HiddenCircuits.Complexity.CanonicalCookComposition
import HiddenCircuits.Complexity.GraphVerifier.FinalRuntime

/-! Complete fixed source counting program, parameterized only by the actual
clone-query emitter code and its independently proved operational endpoint. -/
namespace HiddenCircuits.Complexity.SourceGrid
open OracleBlock Polynomial

noncomputable def program (Q : OracleBlock 29) : OracleBlock 42 := seq setup (seq (loop Q) finish)
noncomputable def time (q : Polynomial ℕ) : Polynomial ℕ := setupTime+loopTime q+finishTime+4

theorem program_executes (Q : OracleBlock 29) (q : Polynomial ℕ)
    (hQ : ∀ (F : CNFInput) (a b : ℕ), ∃ c,
      Q.Executes GraphInput.independentSetProblem (queryStore (CNFInput.encode F) a b [])
        (queryStore (CNFInput.encode F) a b (F.2.2.encodedCloneQuery a b)) c ∧
      c≤q.eval ((CNFInput.encode F).length+a+b)) (F : CNFInput) :
    ∃ s : Store 42, ∃ c, (program Q).Executes GraphInput.independentSetProblem
      (Function.update (fun _ => []) 0 (CNFInput.encode F)) s c ∧
      s 0=Computability.encodeNat F.2.2.satCount ∧ c≤(time q).eval (CNFInput.encode F).length := by
  obtain ⟨a,ha,hab⟩ := setup_executes GraphInput.independentSetProblem F
  obtain ⟨b,hb,hbb⟩ := loop_executes Q q hQ F
  obtain ⟨s,c,hc,ho,hcb⟩ := finish_executes F
  refine ⟨s,a+(b+c+2)+2,seq_executes _ _ _ ha (seq_executes _ _ _ hb hc),ho,?_⟩
  simp only [time,eval_add,eval_ofNat]
  omega

/-- The final instantiation obligation is the canonical clone emitter's actual
byte-level execution, rather than any source hardness or arithmetic premise. -/
theorem independentSet_hard_of_clone_emitter (Q : OracleBlock 29) (q : Polynomial ℕ)
    (hQ : ∀ (F : CNFInput) (a b : ℕ), ∃ c,
      Q.Executes GraphInput.independentSetProblem (queryStore (CNFInput.encode F) a b [])
        (queryStore (CNFInput.encode F) a b (F.2.2.encodedCloneQuery a b)) c ∧
      c≤q.eval ((CNFInput.encode F).length+a+b)) : SharpPHard GraphInput.independentSetProblem :=
  sharpPHard_of_canonical_sat_block GraphInput.independentSetProblem (program Q) (time q)
    (program_executes Q q hQ)

end HiddenCircuits.Complexity.SourceGrid
