import HiddenCircuits.Approximation.SamplerRuntime.Functional
import HiddenCircuits.Approximation.SamplerRuntime.CoreCorrectness

/-! Probability theorem kept separate from the physical runtime. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Functional
open Complexity GraphReduction.MonotoneEndpointEncoding FiniteChains
attribute [local instance] Classical.propDecidable

theorem samplingGuarantee (h : PolyTime evaluate) :
    SamplingGuarantee (randomProgram h) Output.promised Output.solutions := by
  intro x hx k
  obtain ⟨E,rfl⟩ := hx
  let N := (sampleInput (encode E) k).length
  have hn : E.1≤N := by
    have hh := size_le_encode E
    dsimp [N];rw [sampleInput_length];omega
  have hk : k≤N := by dsimp [N];rw [sampleInput_length];omega
  refine ⟨?_,?_,?_⟩
  · intro r w hw
    rw [run_canonical] at hw
    rw [Output.solutions_encode]
    exact Core.evaluate_sound E.2 N _ w hw
  · intro he r
    rw [Output.solutions_encode] at he
    rw [run_canonical]
    exact Core.evaluate_empty E.2 N _ he
  · intro A
    have hh := Core.evaluate_event_error E.2 N k hn hk A
    simp only [Output.solutions_encode,run_canonical]
    rw [bits_eq]
    exact hh
end HiddenCircuits.Approximation.SamplerRuntime.Functional
