import HiddenCircuits.Approximation.SamplerRuntime.GraphOuterCore

namespace HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
open Complexity OracleBlock Polynomial
open Outer (graph tape inputSize preValid unary)
noncomputable def choose : OracleBlock 77 := seq parseGraph (branchPop 7 skip skip core)
noncomputable def dispatch : OracleBlock 77 := branchPop 8 skip skip choose
noncomputable def work : OracleBlock 77 := seq prepare dispatch
noncomputable def workTime : Polynomial ℕ := 50*(X+1)^2+GraphParser.time+coreTime+10

theorem choose_executes (g : BitString → ℕ) (raw : BitString) :
    ∃s : Store 77,∃c,choose.Executes g (beforeParser raw) s c ∧ s 2=chosenValue raw ∧
      c≤GraphParser.time.eval (graph raw).length+coreTime.eval raw.length+5 := by
  obtain ⟨a,ha,hab⟩ := parser_executes g raw
  cases he:GraphInput.decode (graph raw) with
  | none =>
    have hf : postParser raw (7:Fin 78)=false::[] := by simp [postParser,store,GraphParser.output,he]
    have hb := branchPop_false (7:Fin 78) skip skip core g hf (skip_executes g (afterValid raw))
    refine ⟨afterValid raw,_,seq_executes _ _ g ha hb,?_,by omega⟩
    simp [afterValid,postParser,store,chosenValue,he]
  | some G =>
    obtain ⟨s,b,hb,ho,hbb⟩ := core_executes g raw G he
    have hf : postParser raw (7:Fin 78)=true::[] := by simp [postParser,store,GraphParser.output,he]
    have ht := branchPop_true (7:Fin 78) skip skip core g hf hb
    refine ⟨s,_,seq_executes _ _ g ha ht,?_,by omega⟩
    simpa only [chosenValue,he] using ho

theorem dispatch_executes (g : BitString → ℕ) (raw : BitString) :
    ∃s : Store 77,∃c,dispatch.Executes g (prepared raw) s c ∧ s 2=GraphFunctional.evaluate raw ∧
      c≤GraphParser.time.eval (graph raw).length+coreTime.eval raw.length+7 := by
  cases hv:preValid raw with
  | false =>
    have hf : prepared raw (8:Fin 78)=false::[] := by simp [prepared,store,hv]
    have hh := branchPop_false (8:Fin 78) skip skip choose g hf (by rw [pop_prepared];exact skip_executes g (beforeParser raw))
    refine ⟨beforeParser raw,3,hh,?_,by omega⟩
    rw [evaluate_eq,hv]
    rfl
  | true =>
    obtain ⟨s,c,hc,ho,hb⟩ := choose_executes g raw
    have hf : prepared raw (8:Fin 78)=true::[] := by simp [prepared,store,hv]
    have hh := branchPop_true (8:Fin 78) skip skip choose g hf (by rw [pop_prepared];exact hc)
    refine ⟨s,c+2,hh,?_,by omega⟩
    rw [evaluate_eq,hv]
    exact ho

theorem work_executes (g : BitString → ℕ) (raw : BitString) :
    ∃s : Store 77,∃c,work.Executes g (Function.update (fun _ : Fin 78 => ([]:BitString)) 0 raw) s c ∧
      s 2=GraphFunctional.evaluate raw ∧ c≤workTime.eval raw.length := by
  obtain ⟨a,ha,hab⟩ := prepare_executes g raw
  obtain ⟨s,b,hb,ho,hbb⟩ := dispatch_executes g raw
  refine ⟨s,_,seq_executes _ _ g ha hb,ho,?_⟩
  have hp := polynomial_nat_eval_mono GraphParser.time ((Outer.graph_length raw).trans (Outer.inputSize_le raw))
  dsimp only at hp
  simp only [workTime,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  omega
lemma work_queryFree : work.QueryFree := seq_queryFree _ _ prepare_queryFree
  (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree
    (seq_queryFree _ _ parseGraph_queryFree (branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree core_queryFree)))
end HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
