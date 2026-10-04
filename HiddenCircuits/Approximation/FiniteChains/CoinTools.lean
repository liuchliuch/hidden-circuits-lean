import HiddenCircuits.Approximation.FiniteChains.Rational
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
attribute [local instance] Classical.propDecidable
def splitTape (a b : ℕ) : CoinTape (a+b) ≃ CoinTape a × CoinTape b :=
  (Equiv.arrowCongr (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b)).symm
    (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
def tapeNumber (m : ℕ) : CoinTape m ≃ Fin (2^m) :=
  (Equiv.piCongrRight (fun _ : Fin m => finTwoEquiv.symm)).trans finFunctionFinEquiv
noncomputable def coinExpectation (m : ℕ) (f : CoinTape m → ℚ) : ℚ :=
  (∑ r, f r)/(2^m : ℚ)
theorem coinProbability_eq_expectation (m : ℕ) (E : CoinTape m → Prop) :
    coinProbability m E = coinExpectation m (fun r => if E r then 1 else 0) := by
  classical
  unfold coinProbability coinExpectation
  rw [Fintype.card_subtype,Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
theorem coinExpectation_congr (m : ℕ) (f g : CoinTape m → ℚ) (h : ∀ r, f r=g r) :
    coinExpectation m f=coinExpectation m g := by rw [funext h]
@[simp] theorem coinExpectation_const (m : ℕ) (c : ℚ) :
    coinExpectation m (fun _ => c)=c := by
  unfold coinExpectation
  simp [card_coinTape]
theorem coinExpectation_split (a b : ℕ) (f : CoinTape a → CoinTape b → ℚ) :
    coinExpectation (a+b) (fun r => f (splitTape a b r).1 (splitTape a b r).2) =
      coinExpectation a (fun r => coinExpectation b (f r)) := by
  unfold coinExpectation
  rw [(splitTape a b).sum_comp (fun r => f r.1 r.2),Fintype.sum_prod_type]
  rw [pow_add,← Finset.sum_div,div_div]
  ring
theorem coinExpectation_by_output {α : Type*} [Fintype α] (m : ℕ)
    (f : CoinTape m → α) (g : α → ℚ) :
    coinExpectation m (fun r => g (f r)) =
      ∑ x, coinProbability m (fun r => f r=x)*g x := by
  classical
  simp_rw [coinProbability_eq_expectation,coinExpectation,Finset.sum_div,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp [eq_comm,ite_div,ite_mul]
  ring
@[simp] theorem coinProbability_singleton (m : ℕ) (r : CoinTape m) :
    coinProbability m (fun s => s=r)=1/(2^m : ℚ) := by
  classical
  simp [coinProbability]
theorem reciprocal_le_coinProbability (m : ℕ) (E : CoinTape m → Prop)
    (r : CoinTape m) (hr : E r) : 1/(2^m : ℚ) ≤ coinProbability m E := by
  rw [← coinProbability_singleton m r]
  apply coinProbability_mono
  intro s hs
  exact hs ▸ hr
theorem coinProbability_equiv {β : Type*} [Fintype β] (m : ℕ)
    (e : CoinTape m ≃ β) (E : β → Prop) :
    coinProbability m (fun r => E (e r)) =
      (Fintype.card {b : β // E b} : ℚ)/(2^m : ℚ) := by
  classical
  unfold coinProbability
  rw [Fintype.card_congr (Equiv.subtypeEquivOfSubtype e)]
theorem coinProbability_prefix (a b : ℕ) (E : CoinTape a → Prop) :
    coinProbability (a+b) (fun r => E (splitTape a b r).1) = coinProbability a E := by
  rw [coinProbability_eq_expectation,coinProbability_eq_expectation]
  rw [coinExpectation_split a b (fun r _ => if E r then 1 else 0)]
  simp only [coinExpectation_const]
end HiddenCircuits.Approximation.FiniteChains
