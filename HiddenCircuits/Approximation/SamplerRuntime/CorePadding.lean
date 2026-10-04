import HiddenCircuits.Approximation.SamplerRuntime.Core

/-! Finite-tape prefix and padding lemmas, independent of the mixing bound. -/
namespace HiddenCircuits.Approximation.SamplerRuntime
open Complexity GraphReduction.MonotoneEndpointEncoding FiniteChains
attribute [local instance] Classical.propDecidable

namespace Iteration
variable {n : ℕ}

lemma iterate_take (E : MonotoneEndpoints n) (t : ℕ) (π : E.Permutations) (xs : BitString)
    (h : width n*t≤xs.length) : iterate E t π xs=iterate E t π (xs.take (width n*t)) := by
  calc
    iterate E t π xs=iterate E t π (xs.take (width n*t)++xs.drop (width n*t)) := by rw [List.take_append_drop]
    _ = _ := iterate_append E t π _ _ (by simp [List.length_take, min_eq_left h])

lemma iterate_append_of_le (E : MonotoneEndpoints n) (t : ℕ) (π : E.Permutations) (xs ys : BitString)
    (h : width n*t≤xs.length) : iterate E t π (xs++ys)=iterate E t π xs := by
  calc
    _=iterate E t π ((xs++ys).take (width n*t)) := iterate_take E t π _ (by simp;omega)
    _=iterate E t π (xs.take (width n*t)) := by rw [List.take_append_of_le_length h]
    _=iterate E t π xs := (iterate_take E t π xs h).symm

end Iteration

namespace Core

lemma evaluate_append {n : ℕ} (E : MonotoneEndpoints n) (N : ℕ) (xs ys : BitString)
    (h : Iteration.width n*Budget.steps N≤xs.length) : evaluate E N (xs++ys)=evaluate E N xs := by
  cases hi : E.startingPermutation with
  | none => simp [evaluate,hi]
  | some π => simp only [evaluate,hi,Iteration.iterate_append_of_le E _ π xs ys h]

end Core

end HiddenCircuits.Approximation.SamplerRuntime
