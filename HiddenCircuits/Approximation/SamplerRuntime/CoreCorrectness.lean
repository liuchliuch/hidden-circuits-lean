import HiddenCircuits.Approximation.SamplerRuntime.CoreSoundness
import HiddenCircuits.Approximation.SamplerRuntime.BudgetCorrectness

/-! Correctness of the sampler core under its concrete canonical-path budget. -/

/-! Correctness of the sampler core under its concrete canonical-path budget. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Core
open Complexity Complexity.OracleBlock GraphReduction.MonotoneEndpointEncoding
open FiniteChains CoinLists
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma iterate_padded (E : MonotoneEndpoints n) (N : ℕ) (hn : n≤N) (π : E.Permutations)
    (r : CoinTape (Budget.bits N)) :
    Iteration.iterate E (Budget.steps N) π (List.ofFn r)=
      runCoins (MonotoneSwitch.step E (Nat.size n)) (Budget.steps N) π
        (restrictTape (Budget.tape_budget hn) r) := by
  let needed := Iteration.width n*Budget.steps N
  have he : List.ofFn r=List.ofFn (restrictTape (Budget.tape_budget hn) r)++(List.ofFn r).drop needed := by
    rw [restrict_ofFn]
    exact (List.take_append_drop needed (List.ofFn r)).symm
  rw [he,Iteration.iterate_append E _ π _ _ (by simp [Iteration.width]),Iteration.iterate_ofFn]

theorem evaluate_event_error (E : MonotoneEndpoints n) (N k : ℕ) (hn : n≤N) (hk : k≤N)
    (A : Option BitString → Prop) :
    |coinProbability (Budget.bits N) (fun r => A (decodeSample (evaluate E N (List.ofFn r))))-
      uniformProbability (Output.witnesses E) A|≤1/(2^k:ℚ) := by
  cases hi : E.startingPermutation with
  | none =>
    have he : Output.witnesses E=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hh
      exact (E.startingPermutation_none_iff.mp hi) ((Output.witnesses_nonempty E).mp hh)
    simp [evaluate,hi,he,decodeSample,coinProbability_constant]
  | some π =>
    simp only [evaluate,hi,Output.decode_success]
    simp_rw [iterate_padded E N hn π]
    rw [probability_restrict (Budget.tape_budget hn)
      (fun r => A (some (Output.witness (runCoins (MonotoneSwitch.step E (Nat.size n)) (Budget.steps N) π r).val)))]
    rw [Output.uniform_witnesses E π A]
    exact Budget.row_event_error E π N k hn hk (fun x => A (some (Output.witness x.val)))

end HiddenCircuits.Approximation.SamplerRuntime.Core
