import HiddenCircuits.Approximation.FiniteChains.CoinTools
namespace HiddenCircuits.Approximation
open FiniteChains
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FiniteChains
theorem coinExpectation_mono (m : ℕ) (f g : CoinTape m → ℚ) (h : ∀r,f r ≤ g r) :
    coinExpectation m f ≤ coinExpectation m g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => h r)) (by positivity)
theorem coinExpectation_add (m : ℕ) (f g : CoinTape m → ℚ) :
    coinExpectation m (fun r => f r+g r)=coinExpectation m f+coinExpectation m g := by
  simp only [coinExpectation,Finset.sum_add_distrib,add_div]
theorem coinExpectation_sub_const (m : ℕ) (f : CoinTape m → ℚ) (u : ℚ) :
    coinExpectation m (fun r => f r-u)=coinExpectation m f-u := by
  unfold coinExpectation
  rw [Finset.sum_sub_distrib,sub_div]
  simp [card_coinTape]
theorem abs_coinExpectation_le (m : ℕ) (f : CoinTape m → ℚ) :
    |coinExpectation m f| ≤ coinExpectation m (fun r => |f r|) := by
  unfold coinExpectation
  rw [abs_div,abs_of_pos (pow_pos (by norm_num : (0:ℚ)<2) m)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
end FiniteChains
theorem split_experiment_error {a b : ℕ} (E : CoinTape a → CoinTape b → Prop)
    (Bad : CoinTape a → Prop) (u ε δ : ℚ) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hε : 0 ≤ ε)
    (hgood : ∀r,¬Bad r → |coinProbability b (E r)-u| ≤ ε)
    (hbad : coinProbability a Bad ≤ δ) :
    |coinProbability (a+b) (fun r => E (splitTape a b r).1 (splitTape a b r).2)-u| ≤ ε+δ := by
  have he : coinProbability (a+b) (fun r => E (splitTape a b r).1 (splitTape a b r).2)=
      coinExpectation a (fun r => coinProbability b (E r)) := by
    rw [coinProbability_eq_expectation,coinExpectation_split a b (fun r t => if E r t then 1 else 0)]
    apply coinExpectation_congr
    intro r
    exact (coinProbability_eq_expectation b (E r)).symm
  rw [he,← coinExpectation_sub_const]
  calc
    _ ≤ coinExpectation a (fun r => |coinProbability b (E r)-u|) := abs_coinExpectation_le _ _
    _ ≤ coinExpectation a (fun r => ε+(if Bad r then 1 else 0)) := by
      apply coinExpectation_mono
      intro r
      by_cases hr : Bad r
      · simp only [if_pos hr]
        have hp₀ := coinProbability_nonneg b (E r)
        have hp₁ := coinProbability_le_one b (E r)
        rw [abs_le]
        constructor <;> linarith
      · simpa only [if_neg hr,add_zero] using hgood r hr
    _ = ε+coinProbability a Bad := by
      rw [coinExpectation_add,coinExpectation_const,← coinProbability_eq_expectation]
    _ ≤ ε+δ := by linarith
def initializeAndSample {α : Type*} {a b : ℕ} (init : CoinTape a → Option α)
    (sample : α → CoinTape b → α) (r : CoinTape (a+b)) : Option α :=
  (init (splitTape a b r).1).map (fun s => sample s (splitTape a b r).2)
theorem initializeAndSample_error {α : Type*} {a b : ℕ}
    (init : CoinTape a → Option α) (sample : α → CoinTape b → α)
    (E : Option α → Prop) (u ε δ : ℚ) (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hε : 0 ≤ ε)
    (hmix : ∀s,|coinProbability b (fun r => E (some (sample s r)))-u| ≤ ε)
    (hinit : coinProbability a (fun r => init r=none) ≤ δ) :
    |coinProbability (a+b) (fun r => E (initializeAndSample init sample r))-u| ≤ ε+δ := by
  apply split_experiment_error (fun r t => E ((init r).map (fun s => sample s t)))
    (fun r => init r=none) u ε δ hu₀ hu₁ hε ?_ hinit
  intro r hr
  cases hs : init r with
  | none => exact False.elim (hr hs)
  | some s => simpa only [hs,Option.map_some] using hmix s
theorem initializeAndSample_empty {α : Type*} [IsEmpty α] {a b : ℕ}
    (init : CoinTape a → Option α) (sample : α → CoinTape b → α)
    (r : CoinTape (a+b)) : initializeAndSample init sample r=none := by
  unfold initializeAndSample
  cases init (splitTape a b r).1 with
  | none => rfl
  | some s => exact isEmptyElim s
end HiddenCircuits.Approximation
