import HiddenCircuits.Approximation.SamplerRuntime.MonotoneProgram
import HiddenCircuits.Approximation.SamplerRuntime.FunctionalCorrectness

/-! The actual 45-stack runtime instantiated in the unconditional FPAUS. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.MonotoneSampler

theorem samplingGuarantee : SamplingGuarantee randomProgram Output.promised Output.solutions :=
  Functional.samplingGuarantee evaluate_polyTime

theorem hasFPAUS : HasFPAUS Output.promised Output.solutions := ⟨randomProgram,samplingGuarantee⟩
end HiddenCircuits.Approximation.SamplerRuntime.MonotoneSampler
