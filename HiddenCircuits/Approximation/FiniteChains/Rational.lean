import HiddenCircuits.Approximation.FiniteChains.Events
import HiddenCircuits.Approximation.SwitchChain

/-! Exact rational and fair-bit transition tables embed in the real analysis. -/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
variable {α : Type*} [Fintype α]

noncomputable def LazyChain.ofRational (w : α → α → ℚ)
    (hn : ∀ x y, 0 ≤ w x y) (hs : ∀ x, ∑ y, w x y = 1)
    (hsy : ∀ x y, w x y=w y x) (hl : ∀ x, (1:ℚ)/2 ≤ w x x) : LazyChain α where
  weight x y := w x y
  nonneg x y := by exact_mod_cast hn x y
  row_sum x := by exact_mod_cast hs x
  symmetric x y := by exact_mod_cast hsy x y
  lazy x := by
    have h : ((1/2:ℚ):ℝ) ≤ (w x x:ℝ) := Rat.cast_le.mpr (hl x)
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h

/-- A concrete fixed-bit involutive step determines a chain, when its holding
probability has been verified. It uses the already proved counting formulas. -/
noncomputable def LazyChain.ofCoinStep (m : ℕ) (step : α → CoinTape m → α)
    (hinv : ∀ r, Function.Involutive (fun x => step x r))
    (hlazy : ∀ x, (1:ℚ)/2 ≤ transitionProbability m step x x) : LazyChain α :=
  LazyChain.ofRational (transitionProbability m step)
    (fun _ _ => coinProbability_nonneg _ _) (transitionProbability_sum m step)
    (transitionProbability_symmetric m step hinv) hlazy

@[simp] theorem LazyChain.ofCoinStep_weight (m : ℕ) (step : α → CoinTape m → α)
    (hinv : ∀ r, Function.Involutive (fun x => step x r))
    (hlazy : ∀ x, (1:ℚ)/2 ≤ transitionProbability m step x x) (x y : α) :
    (LazyChain.ofCoinStep m step hinv hlazy).weight x y =
      (transitionProbability m step x y : ℝ) := rfl

end HiddenCircuits.Approximation.FiniteChains
