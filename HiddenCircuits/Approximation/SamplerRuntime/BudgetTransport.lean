import HiddenCircuits.Approximation.FiniteChains.CoinRealization
import HiddenCircuits.Approximation.FiniteChains.Orientation

/-! Exact column/row finite-tape transport, independent of concrete path construction. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Budget
open FiniteChains FiniteChains.MonotoneSwitch

lemma inverse_run {n : ℕ} (E : MonotoneEndpoints n) (m t : ℕ) (s : ColumnState E)
    (r : CoinTape ((1+(m+m))*t)) :
    inverseEquiv E (runCoins (columnStep E m) t s r)=runCoins (MonotoneSwitch.step E m) t (inverseEquiv E s) r := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [runCoins,columnStep,Equiv.apply_symm_apply,ih]

end HiddenCircuits.Approximation.SamplerRuntime.Budget
