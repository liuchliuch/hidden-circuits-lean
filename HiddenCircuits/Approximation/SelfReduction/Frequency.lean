import HiddenCircuits.Approximation.FiniteCoins
import HiddenCircuits.Approximation.SelfReduction.Concentration
import HiddenCircuits.Approximation.SelfReduction.Amplification
import HiddenCircuits.Approximation.SelfReduction.RobustEstimate

/-! An explicit frequency estimator with 2T² samples per group and 2(k+1)
independent groups. Its error and confidence are derived from finite sums. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

 def batchSize (T : ℕ) : ℕ := 2*T^2

 def eventFrequency {α : Type*} (n : ℕ) (E : α → Prop) [DecidablePred E]
    (r : Fin n → α) : ℚ :=
  ((Finset.univ.filter (fun i => E (r i))).card : ℚ)/(n : ℚ)

 theorem eventFrequency_eq_average {α : Type*} (n : ℕ) (E : α → Prop) [DecidablePred E]
    (r : Fin n → α) : eventFrequency n E r=sampleAverage n (fun a => if E a then 1 else 0) r := by
  simp only [eventFrequency, sampleAverage, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

 theorem eventFrequency_failure {α : Type*} [Fintype α] [Nonempty α]
    (E : α → Prop) [DecidablePred E] (T : ℕ) (hT : 0<T) :
    probability (fun r : Fin (batchSize T) → α =>
      1/(T : ℚ) < |eventFrequency (batchSize T) E r-probability E|) ≤ 1/8 := by
  have ht : (0 : ℚ)<T := by exact_mod_cast hT
  have hn : 0<batchSize T := by unfold batchSize; positivity
  have hh := sampleAverage_chebyshev (fun a => if E a then (1 : ℚ) else 0)
    (fun a => by dsimp only; split_ifs <;> norm_num) (batchSize T) hn (1/(T : ℚ)) (by positivity)
  have hp : mean (fun a : α => if E a then (1 : ℚ) else 0)=probability E := by
    exact mean_indicator E
  simp_rw [← eventFrequency_eq_average, hp] at hh
  convert hh using 1
  unfold batchSize
  push_cast
  field_simp
  <;> ring

 def amplifiedFrequency {α : Type*} (E : α → Prop) [DecidablePred E] (T k : ℕ)
    (r : Fin (2*(k+1)) → Fin (batchSize T) → α) : ℚ :=
  let z : Fin (2*k+1+1) → ℚ :=
    fun i => eventFrequency (batchSize T) E (r (Fin.cast (by omega) i))
  robustEstimate (2*k+1) z (2/(T : ℚ))

 theorem card_filter_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (E : β → Prop) [DecidablePred E] :
    (Finset.univ.filter (fun a => E (e a))).card=(Finset.univ.filter E).card := by
  simp only [Finset.card_filter]
  exact Equiv.sum_comp e (fun b => if E b then (1 : ℕ) else 0)

/-- A near-uniform sampler with bias at most 1/T yields an observed estimator
within 6/T, except on probability at most 2^(-(k+1)). -/
 theorem amplifiedFrequency_failure {α : Type*} [Fintype α] [Nonempty α]
    (E : α → Prop) [DecidablePred E] (T : ℕ) (hT : 0<T) (k : ℕ) (p : ℚ)
    (hbias : |probability E-p| ≤ 1/(T : ℚ)) :
    probability (fun r => 6/(T : ℚ) < |amplifiedFrequency E T k r-p|) ≤ 1/(2^(k+1) : ℚ) := by
  let bad : (Fin (batchSize T) → α) → Prop := fun r => 2/(T : ℚ) < |eventFrequency (batchSize T) E r-p|
  have hbad : probability bad ≤ 1/8 := by
    apply le_trans _ (eventFrequency_failure E T hT)
    apply probability_mono
    intro r hr
    dsimp [bad] at hr
    by_contra hn
    have hh := le_of_not_gt hn
    have ht : |eventFrequency (batchSize T) E r-p| ≤
        |eventFrequency (batchSize T) E r-probability E|+|probability E-p| := by
      simpa using abs_sub_le (eventFrequency (batchSize T) E r) (probability E) p
    apply (not_lt_of_ge (ht.trans (add_le_add hh hbias)))
    convert hr using 1 <;> ring
  apply le_trans _ (majority_failure_bound bad hbad (k+1))
  apply probability_mono
  intro r hr
  by_contra hn
  have hcard : (Finset.univ.filter (fun i => bad (r i))).card<k+1 := Nat.lt_of_not_ge hn
  let z : Fin (2*k+1+1) → ℚ := fun i => eventFrequency (batchSize T) E (r (Fin.cast (by omega) i))
  have he : (Finset.univ.filter (fun i => 2/(T : ℚ) < |z i-p|)).card=
      (Finset.univ.filter (fun i => bad (r i))).card := by
    exact card_filter_equiv (finCongr (by omega : 2*k+1+1=2*(k+1))) (fun i => bad (r i))
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin (2*k+1+1) => |z i-p| ≤ 2/(T : ℚ))
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at hsplit
  have hmajor : 2*k+1+1<2*(Finset.univ.filter (fun i => |z i-p| ≤ 2/(T : ℚ))).card := by omega
  have hh := robustEstimate_accurate (2*k+1) z p (2/(T : ℚ)) hmajor
  change 6/(T : ℚ) < |robustEstimate (2*k+1) z (2/(T : ℚ))-p| at hr
  apply (not_lt_of_ge hh)
  convert hr using 1 <;> ring

 theorem probability_coinTape (m : ℕ) (E : CoinTape m → Prop) :
    probability E=coinProbability m E := by
  classical
  unfold probability mean coinProbability
  rw [Fintype.card_subtype, Finset.card_filter, card_coinTape]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_pow, Nat.cast_ofNat]

end HiddenCircuits.Approximation.SelfReduction
