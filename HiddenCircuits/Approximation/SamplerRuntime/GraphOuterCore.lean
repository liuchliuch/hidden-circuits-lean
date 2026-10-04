import HiddenCircuits.Approximation.SamplerRuntime.GraphOuterCoreEntry
import HiddenCircuits.Approximation.Initialization.SamplerInterface

/-! Unconditional general-graph sampler core, assembling the
literal tape splitter, concrete matching initializer, and partner-chain runner.
No supplied matching, initializer hypothesis, or runtime certificate remains. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
open Complexity Complexity.OracleBlock Polynomial
open Outer (graph tape inputSize preValid unary)
set_option maxHeartbeats 2000000

noncomputable def core : OracleBlock 77 := seq GraphOuterCorePreparation.program
  (PartnerInitialized.program Initialization.SamplerInterface.program)
noncomputable def coreTime : Polynomial ℕ :=
  (GraphOuterCorePreparation.time+PartnerInitialized.time Initialization.SamplerInterface.time).comp (X+1)+
    80*(X+1)+2

/-- The machine operates on every source tape, with false padding on any
missing initialization or chain bits, exactly as GraphFunctional.core does. -/
theorem core_executes (g : BitString → ℕ) (raw : BitString) (G : GraphInput)
    (he : GraphInput.decode (graph raw)=some G) :
    ∃ s : Store 77,∃t,core.Executes g (afterValid raw) s t ∧
      s 2=GraphFunctional.core G.2 (inputSize raw+1) (tape raw) ∧ t≤coreTime.eval raw.length := by
  obtain ⟨hn0,hpayload⟩ := core_entry_bounds raw G he
  have hn : G.1 ≤ inputSize raw+1 := by omega
  obtain ⟨a,ha,hab⟩ := GraphOuterCorePreparation.program_executes g (graph raw) G.2.bits G.1
    (inputSize raw) (tape raw)
  rw [←core_entry raw G he] at ha
  obtain ⟨s,b,hb,ho,hbb⟩ := PartnerInitialized.program_executes
    Initialization.SamplerInterface.program Initialization.SamplerInterface.time Initialization.SamplerInterface.init
    Initialization.SamplerInterface.spec g G.2 (inputSize raw+1) hn
    (TapeRead.takePadded (3*(inputSize raw+1)^4) (tape raw))
    ((tape raw).drop (3*(inputSize raw+1)^4)) (by simp [TapeRead.prefix_length])
  refine ⟨s,_,seq_executes _ _ g ha hb,ho,?_⟩
  have hraw := Outer.inputSize_le raw
  have hgraph := (Outer.graph_length raw).trans hraw
  have htape := Outer.tape_length raw
  have hmono := polynomial_nat_eval_mono
    (GraphOuterCorePreparation.time+PartnerInitialized.time Initialization.SamplerInterface.time)
    (show inputSize raw+1≤raw.length+1 by omega)
  change (GraphOuterCorePreparation.time+PartnerInitialized.time Initialization.SamplerInterface.time).eval
      (inputSize raw+1)≤
    (GraphOuterCorePreparation.time+PartnerInitialized.time Initialization.SamplerInterface.time).eval
      (raw.length+1) at hmono
  simp only [eval_add] at hmono
  simp only [coreTime,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
  omega

lemma core_queryFree : core.QueryFree := seq_queryFree _ _ GraphOuterCorePreparation.program_queryFree
  (PartnerInitialized.program_queryFree Initialization.SamplerInterface.program
    Initialization.SamplerInterface.time Initialization.SamplerInterface.init Initialization.SamplerInterface.spec)
end HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
