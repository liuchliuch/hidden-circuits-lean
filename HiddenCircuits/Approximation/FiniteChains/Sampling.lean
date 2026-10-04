import HiddenCircuits.Approximation.FiniteChains.CoinRealization
import HiddenCircuits.Approximation.FiniteChains.Orientation
namespace HiddenCircuits.Approximation.FiniteChains.MonotoneSwitch
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (E : MonotoneEndpoints n) {K L : ℕ}
theorem column_sampling_error
    (C : CanonicalPaths (columnChain E (Nat.size n)) K L (8*(n+1)^2))
    (k : ℕ) (s : ColumnState E) (A : ColumnState E → Prop) :
    |coinProbability ((1+(Nat.size n+Nat.size n))*C.mixingSteps (n^2) k)
        (fun r => A (runCoins (columnStep E (Nat.size n)) (C.mixingSteps (n^2) k) s r)) -
      (Fintype.card {x : ColumnState E // A x} : ℚ)/Fintype.card (ColumnState E)| ≤
      1/(2^k : ℚ) := by
  letI : Nonempty (ColumnState E) := ⟨s⟩
  exact runCoins_event_error (columnStep E (Nat.size n))
    (columnStep_involutive E (Nat.size n)) (columnStep_lazy E (Nat.size n))
    C (n^2) k (card_columnStates_le E) s A
theorem sampling_bits_le
    (C : CanonicalPaths (columnChain E (Nat.size n)) K L (8*(n+1)^2)) (k : ℕ) :
    (1+(Nat.size n+Nat.size n))*C.mixingSteps (n^2) k ≤
      (1+2*n)*(2*(1+L*(8*(n+1)^2)*K)*(n^2+2*k)) := by
  have hw := proposal_width_le (n := n)
  have hs : max 1 (L*(8*(n+1)^2)*K) ≤ 1+L*(8*(n+1)^2)*K := by omega
  unfold CanonicalPaths.mixingSteps CanonicalPaths.scale
  apply Nat.mul_le_mul
  · omega
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hs)
end HiddenCircuits.Approximation.FiniteChains.MonotoneSwitch
