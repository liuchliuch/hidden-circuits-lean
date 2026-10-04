import HiddenCircuits.Approximation.SamplerRuntime.GraphOuterDispatch
import HiddenCircuits.Approximation.RealOrderedIntervals

/-! Unconditional general quasimonotone and real unit-interval FPAUS, through
one actual raw-input finite TM2 program with no supplied initializer. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphSampler
open Complexity OracleBlock Polynomial GraphReduction
noncomputable def program : OracleBlock 77 := seq GraphOuter.work (cleanResult 2 1 (by decide) (by decide))
noncomputable def time : Polynomial ℕ := GraphOuter.workTime+82*(X+GraphOuter.workTime+3)+3

theorem program_executes (g : BitString → ℕ) (raw : BitString) :
    ∃c,program.Executes g (Function.update (fun _ : Fin 78 => ([]:BitString)) 0 raw)
      (Function.update (fun _ : Fin 78 => ([]:BitString)) 0 (GraphFunctional.evaluate raw)) c ∧ c≤time.eval raw.length := by
  obtain ⟨s,a,ha,ho,hab⟩ := GraphOuter.work_executes g raw
  have hs := ha.stack_bound (GraphOuter.work.machine.init_stack_bound raw)
  obtain ⟨b,hb,hbb⟩ := cleanResult_executes g (2:Fin 78) 1 (by decide) (by decide) (by decide)
    s (raw.length+a) hs
  rw [ho] at hb
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  omega
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ GraphOuter.work_queryFree (cleanResult_queryFree _ _ _ _)

theorem evaluate_polyTime : PolyTime GraphFunctional.evaluate := by
  apply polyTime_of_block program program_queryFree time
  intro raw
  obtain ⟨c,hc,hb⟩ := program_executes (fun _ => 0) raw
  exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩
noncomputable def randomProgram : RandomBitProgram := GraphFunctional.randomProgram evaluate_polyTime

theorem samplingGuarantee : SamplingGuarantee randomProgram GraphFunctional.promised GraphFunctional.solutions :=
  GraphFunctional.samplingGuarantee evaluate_polyTime

theorem quasimonotone_hasFPAUS : HasFPAUS GraphFunctional.promised GraphFunctional.solutions :=
  ⟨randomProgram,samplingGuarantee⟩

def realUnitPromised (xs : BitString) : Prop :=
  ∃G : GraphInput,G.encode=xs ∧ GraphReduction.RealUnitInterval.UnitIntervalGraph G.2.graph

theorem realUnit_samplingGuarantee : SamplingGuarantee randomProgram realUnitPromised GraphFunctional.solutions := by
  intro xs hx k
  obtain ⟨G,hG,hr⟩ := hx
  exact samplingGuarantee xs ⟨G,hG,realUnitIntervalGraph_quasimonotone hr⟩ k

theorem realUnit_hasFPAUS : HasFPAUS realUnitPromised GraphFunctional.solutions := ⟨randomProgram,realUnit_samplingGuarantee⟩

/-- Clean canonical call interface for the graph counting batch compiler. -/
theorem canonical_executes (g : BitString → ℕ) (G : GraphInput) (k : ℕ) (tape : BitString) :
    ∃c,program.Executes g (Function.update (fun _ : Fin 78 => ([]:BitString)) 0 (pairBits (sampleInput G.encode k) tape))
      (Function.update (fun _ : Fin 78 => ([]:BitString)) 0 (GraphFunctional.core G.2 ((sampleInput G.encode k).length+1) tape)) c ∧
      c≤time.eval (pairBits (sampleInput G.encode k) tape).length := by
  simpa only [GraphFunctional.evaluate_canonical] using program_executes g (pairBits (sampleInput G.encode k) tape)
end HiddenCircuits.Approximation.SamplerRuntime.GraphSampler
