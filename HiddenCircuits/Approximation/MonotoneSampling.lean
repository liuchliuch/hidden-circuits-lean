import HiddenCircuits.Approximation.CanonicalPaths.MonotoneFlow
namespace HiddenCircuits.Approximation.MonotoneSampling
open CanonicalPaths FiniteChains FiniteChains.MonotoneSwitch
attribute [local instance] Classical.propDecidable
def steps (n k : ℕ) : ℕ :=
  2*max 1 (routeLength n*(8*(n+1)^2)*routeTrafficFactor n)*(n^2+2*k)
def bits (n k : ℕ) : ℕ := (1+(Nat.size n+Nat.size n))*steps n k
def sample {n : ℕ} (E : MonotoneEndpoints n) (k : ℕ) (s : ColumnState E)
    (r : CoinTape (bits n k)) : ColumnState E :=
  runCoins (columnStep E (Nat.size n)) (steps n k) s r
theorem sample_event_error {n : ℕ} (E : MonotoneEndpoints n) (k : ℕ)
    (s : ColumnState E) (A : ColumnState E → Prop) :
    |coinProbability (bits n k) (fun r => A (sample E k s r)) -
      (Fintype.card {x : ColumnState E // A x} : ℚ)/Fintype.card (ColumnState E)| ≤ 1/(2^k : ℚ) := by
  simpa only [bits,steps,sample,FiniteChains.CanonicalPaths.mixingSteps,FiniteChains.CanonicalPaths.scale] using
    column_sampling_error E (monotoneCanonicalPaths E) k s A
theorem bits_le (n k : ℕ) :
    bits n k ≤ (1+2*n)*(2*(1+routeLength n*(8*(n+1)^2)*routeTrafficFactor n)*(n^2+2*k)) := by
  have hw := proposal_width_le (n := n)
  have hs : max 1 (routeLength n*(8*(n+1)^2)*routeTrafficFactor n) ≤
      1+routeLength n*(8*(n+1)^2)*routeTrafficFactor n := by omega
  unfold bits steps
  apply Nat.mul_le_mul
  · omega
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hs)
def initialState {n : ℕ} (E : MonotoneEndpoints n) : Option (ColumnState E) :=
  E.startingPermutation.map (inverseEquiv E).symm
theorem initialState_none_iff {n : ℕ} (E : MonotoneEndpoints n) :
    initialState E=none ↔ ¬Nonempty (ColumnState E) := by
  rw [initialState,Option.map_eq_none_iff,E.startingPermutation_none_iff]
  exact not_congr (Equiv.nonempty_congr (inverseEquiv E).symm)
end HiddenCircuits.Approximation.MonotoneSampling
