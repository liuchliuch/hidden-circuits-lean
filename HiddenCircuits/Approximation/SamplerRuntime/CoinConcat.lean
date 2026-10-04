import HiddenCircuits.Approximation.SamplerRuntime.CoinLists
import HiddenCircuits.Approximation.FiniteChains.CoinTools

/-! The original partner loop's additional list/tape concatenation interface. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.CoinLists
open FiniteChains
lemma splitTape_ofFn (a b : ℕ) (r : CoinTape (a+b)) :
    List.ofFn r=List.ofFn ((splitTape a b r).1)++List.ofFn ((splitTape a b r).2) := by
  rw [List.ofFn_add]
  rfl
end HiddenCircuits.Approximation.SamplerRuntime.CoinLists
