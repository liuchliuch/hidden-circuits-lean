import HiddenCircuits.Approximation.FiniteChains.CoinTools

/-!
# Actual bounded random tapes realize the finite chain

Repeated transitions use exactly `m*n` fair bits. The distribution equality
and all-events error below are proved by counting and splitting finite tapes.
These theorems make no claim yet about a TM implementation's running time.
-/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

/-- Execute `n` fixed-bit transitions, using every supplied block once. -/
def runCoins {m : ℕ} (step : α → CoinTape m → α) :
    (n : ℕ) → α → CoinTape (m*n) → α
  | 0, s, _ => s
  | n+1, s, r =>
      let blocks := splitTape (m*n) m r
      step (runCoins step n s blocks.1) blocks.2

noncomputable def runProbability {m : ℕ} (step : α → CoinTape m → α)
    (n : ℕ) (s t : α) : ℚ := coinProbability (m*n) (fun r => runCoins step n s r=t)

/-- The literal random-tape experiment satisfies the Chapman–Kolmogorov step. -/
theorem runProbability_succ {m : ℕ} (step : α → CoinTape m → α)
    (n : ℕ) (s t : α) :
    runProbability step (n+1) s t = ∑ x, runProbability step n s x *
      transitionProbability m step x t := by
  classical
  unfold runProbability
  rw [coinProbability_eq_expectation]
  change coinExpectation (m*n+m) (fun r =>
    if step (runCoins step n s (splitTape (m*n) m r).1) (splitTape (m*n) m r).2=t
      then 1 else 0) = _
  rw [coinExpectation_split (m*n) m (fun r q =>
    if step (runCoins step n s r) q=t then 1 else 0)]
  have hi : ∀ r : CoinTape (m*n), coinExpectation m
      (fun q => if step (runCoins step n s r) q=t then 1 else 0) =
      transitionProbability m step (runCoins step n s r) t := by
    intro r
    exact (coinProbability_eq_expectation m _).symm
  simp_rw [hi]
  exact coinExpectation_by_output (m*n) (runCoins step n s)
    (fun x => transitionProbability m step x t)

/-- Equality with the analyzed Markov-chain law, at every time and state. -/
theorem runProbability_eq_law {m : ℕ} (step : α → CoinTape m → α)
    (hinv : ∀ r, Function.Involutive (fun x => step x r))
    (hlazy : ∀ x, (1:ℚ)/2 ≤ transitionProbability m step x x)
    (n : ℕ) (s t : α) :
    (runProbability step n s t : ℝ) = (LazyChain.ofCoinStep m step hinv hlazy).law n s t := by
  classical
  let P := LazyChain.ofCoinStep m step hinv hlazy
  change (runProbability step n s t : ℝ)=P.law n s t
  induction n generalizing t with
  | zero =>
    by_cases h : s=t <;> simp [runProbability,runCoins,coinProbability_constant,
      LazyChain.law,LazyChain.pointMass,h,eq_comm]
  | succ n ih =>
    rw [runProbability_succ,P.law_succ]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    rw [ih]
    rfl

/-- Push an arbitrary event through the exact finite-tape distribution. -/
theorem run_event_eq_law {m : ℕ} (step : α → CoinTape m → α)
    (hinv : ∀ r, Function.Involutive (fun x => step x r))
    (hlazy : ∀ x, (1:ℚ)/2 ≤ transitionProbability m step x x)
    (n : ℕ) (s : α) (E : α → Prop) :
    (coinProbability (m*n) (fun r => E (runCoins step n s r)) : ℝ) =
      eventMass ((LazyChain.ofCoinStep m step hinv hlazy).law n s) E := by
  classical
  rw [coinProbability_eq_expectation,coinExpectation_by_output (m*n)
    (runCoins step n s) (fun x => if E x then 1 else 0)]
  push_cast
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x
  · simpa only [if_pos hx,Rat.cast_one,mul_one] using
      runProbability_eq_law step hinv hlazy n s x
  · simp [hx]

theorem uniform_event_eq_card (P : LazyChain α) (E : α → Prop) :
    eventMass P.uniform E =
      ((Fintype.card {x : α // E x} : ℚ)/(Fintype.card α : ℚ) : ℝ) := by
  classical
  unfold eventMass LazyChain.uniform
  rw [Fintype.card_subtype,Finset.card_filter]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- A real mixing theorem yields the exact rational all-events guarantee for
an explicitly bounded Boolean-tape experiment. -/
theorem runCoins_event_error [Nonempty α] {m : ℕ} (step : α → CoinTape m → α)
    (hinv : ∀ r, Function.Involutive (fun x => step x r))
    (hlazy : ∀ x, (1:ℚ)/2 ≤ transitionProbability m step x x)
    {K L Q : ℕ} (C : CanonicalPaths (LazyChain.ofCoinStep m step hinv hlazy) K L Q)
    (B k : ℕ) (hcard : Fintype.card α ≤ 2^B) (s : α) (E : α → Prop) :
    |coinProbability (m*C.mixingSteps B k)
        (fun r => E (runCoins step (C.mixingSteps B k) s r)) -
      (Fintype.card {x : α // E x} : ℚ)/(Fintype.card α : ℚ)| ≤ 1/(2^k : ℚ) := by
  have h := C.event_error_le_dyadic B k hcard s E
  rw [← run_event_eq_law step hinv hlazy,uniform_event_eq_card] at h
  have he : ((1:ℝ)/2)^k=1/(2^k:ℝ) := by rw [div_pow,one_pow]
  rw [he] at h
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end HiddenCircuits.Approximation.FiniteChains
