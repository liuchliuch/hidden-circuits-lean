import HiddenCircuits.Approximation.SamplerRuntime.Core

/-! Soundness and empty-instance behavior of the sampler core. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Core
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding
open FiniteChains CoinLists
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem evaluate_sound (E : MonotoneEndpoints n) (N : ℕ) (tape w : BitString)
    (h : decodeSample (evaluate E N tape)=some w) : w∈Output.witnesses E := by
  cases hi : E.startingPermutation with
  | none => simp [evaluate,hi,decodeSample] at h
  | some π =>
    have he : Output.witness (Iteration.iterate E (Budget.steps N) π tape).val=w := by
      simpa [evaluate,hi] using h
    rw [←he]
    exact Output.witness_mem E _

theorem evaluate_empty (E : MonotoneEndpoints n) (N : ℕ) (tape : BitString)
    (h : Output.witnesses E=∅) : decodeSample (evaluate E N tape)=none := by
  have hn : ¬Nonempty E.Permutations := by
    intro hs
    have hh := (Output.witnesses_nonempty E).mpr hs
    simpa [h] using hh
  have hi := E.startingPermutation_none_iff.mpr hn
  simp [evaluate,hi,decodeSample]

end HiddenCircuits.Approximation.SamplerRuntime.Core
