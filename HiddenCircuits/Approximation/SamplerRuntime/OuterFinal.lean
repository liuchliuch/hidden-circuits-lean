import HiddenCircuits.Approximation.SamplerRuntime.OuterDispatch

/-! Actual final result movement and complete
work-stack cleanup, charged by the operational storage bound. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Outer
open Complexity OracleBlock Polynomial

noncomputable def cleanProgram (B : OracleBlock 35) : OracleBlock 44 :=
  seq (work B) (cleanResult 7 2 (by decide) (by decide))
noncomputable def cleanTime (p : Polynomial ℕ) : Polynomial ℕ :=
  workTime p+49*(X+workTime p+3)+3

theorem cleanProgram_executes (B : OracleBlock 35) (p : Polynomial ℕ) (hB : ParserSpec B p)
    (g : BitString → ℕ) (raw : BitString) :
    ∃c,(cleanProgram B).Executes g
      (Function.update (fun _ : Fin 45 => ([]:BitString)) 0 raw)
      (Function.update (fun _ : Fin 45 => ([]:BitString)) 0 (Functional.evaluate raw)) c ∧
      c≤(cleanTime p).eval raw.length := by
  obtain ⟨s,a,ha,ho,hzero,hab⟩ := work_executes B p hB g raw
  have hs := ha.stack_bound ((work B).machine.init_stack_bound raw)
  obtain ⟨b,hb,hbb⟩ := cleanResult_executes g (7:Fin 45) 2 (by decide) (by decide) (by decide)
    s (raw.length+a) hs
  rw [ho] at hb
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [cleanTime,eval_add,eval_mul,eval_X,eval_ofNat]
  omega

lemma cleanProgram_queryFree (B : OracleBlock 35) (p : Polynomial ℕ) (hB : ParserSpec B p) :
    (cleanProgram B).QueryFree :=
  seq_queryFree _ _ (work_queryFree B p hB) (cleanResult_queryFree _ _ _ _)
end HiddenCircuits.Approximation.SamplerRuntime.Outer
