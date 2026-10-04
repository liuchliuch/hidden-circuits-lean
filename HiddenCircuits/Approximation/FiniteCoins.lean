import HiddenCircuits.Complexity.SharpP
namespace HiddenCircuits.Approximation
open scoped BigOperators
abbrev CoinTape (m : ℕ) := Fin m → Bool
@[simp] theorem card_coinTape (m : ℕ) : Fintype.card (CoinTape m) = 2^m := by
  simp [CoinTape]
noncomputable def coinProbability (m : ℕ) (E : CoinTape m → Prop) : ℚ := by
  classical
  exact (Fintype.card {r : CoinTape m // E r} : ℚ) / (2^m : ℚ)
theorem coinProbability_nonneg (m : ℕ) (E : CoinTape m → Prop) :
    0 ≤ coinProbability m E := by
  unfold coinProbability
  positivity
theorem coinProbability_le_one (m : ℕ) (E : CoinTape m → Prop) :
    coinProbability m E ≤ 1 := by
  classical
  have h := Fintype.card_le_of_injective
    (Subtype.val : {r : CoinTape m // E r} → CoinTape m) Subtype.val_injective
  rw [card_coinTape] at h
  unfold coinProbability
  rw [div_le_one (by positivity : (0:ℚ)<2^m)]
  exact_mod_cast h
@[simp] theorem coinProbability_true (m : ℕ) :
    coinProbability m (fun _ => True) = 1 := by
  simp [coinProbability, CoinTape]
@[simp] theorem coinProbability_false (m : ℕ) :
    coinProbability m (fun _ => False) = 0 := by
  simp [coinProbability]
theorem coinProbability_congr {m : ℕ} {E F : CoinTape m → Prop}
    (h : ∀ r, E r ↔ F r) : coinProbability m E = coinProbability m F := by
  have he : E=F := funext fun r => propext (h r)
  rw [he]
theorem coinProbability_mono {m : ℕ} {E F : CoinTape m → Prop}
    (h : ∀ r, E r → F r) : coinProbability m E ≤ coinProbability m F := by
  classical
  have hc := Fintype.card_le_of_injective
    (fun r : {r : CoinTape m // E r} => (⟨r.val,h r.val r.property⟩ : {r // F r}))
    (fun _ _ hh => Subtype.ext (congrArg (fun z : {r : CoinTape m // F r} => z.val) hh))
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
theorem coinProbability_eq_zero_iff (m : ℕ) (E : CoinTape m → Prop) :
    coinProbability m E = 0 ↔ ∀ r, ¬E r := by
  classical
  simp only [coinProbability, div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
    false_and, or_false, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
  constructor
  · intro h r hr
    exact h.false ⟨r,hr⟩
  · intro h
    exact ⟨fun r => h r.val r.property⟩
theorem coinProbability_constant (m : ℕ) (P : Prop) [Decidable P] :
    coinProbability m (fun _ => P) = if P then 1 else 0 := by
  by_cases h : P
  · simp only [if_pos h]
    rw [coinProbability_congr (fun _ => iff_true_intro h), coinProbability_true]
  · simp only [if_neg h]
    rw [coinProbability_congr (fun _ => iff_false_intro h), coinProbability_false]
end HiddenCircuits.Approximation
