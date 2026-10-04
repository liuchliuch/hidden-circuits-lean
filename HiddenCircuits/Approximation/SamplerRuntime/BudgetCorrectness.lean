import HiddenCircuits.Approximation.SamplerRuntime.Budget
import HiddenCircuits.Approximation.SamplerRuntime.BudgetTransport
import HiddenCircuits.Approximation.MonotoneSampling

/-! The executable Budget is independent of this mathematical file. This proof
requires the actual concrete canonical paths, never a supplied mixing certificate. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Budget
open CanonicalPaths FiniteChains FiniteChains.MonotoneSwitch Polynomial
attribute [local instance] Classical.propDecidable

noncomputable def paths {n : ℕ} (E : MonotoneEndpoints n) (N : ℕ) (hn : n≤N) :
    FiniteChains.CanonicalPaths (columnChain E (Nat.size n)) (traffic N+1) (length N+1) (8*(N+1)^2) where
  path := (monotoneCanonicalPaths E).path
  length_le x y := ((monotoneCanonicalPaths E).length_le x y).trans ((length_mono hn).trans (by omega))
  traffic_le x y := ((monotoneCanonicalPaths E).traffic_le x y).trans
    (Nat.mul_le_mul_right _ ((traffic_mono hn).trans (by omega)))
  Q_pos := by positivity
  transition_lower x y i := by
    refine le_trans ?_ ((monotoneCanonicalPaths E).transition_lower x y i)
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast (show 8*(n+1)^2≤8*(N+1)^2 by gcongr)

lemma paths_steps {n : ℕ} (E : MonotoneEndpoints n) [Nonempty (ColumnState E)] (N : ℕ) (hn : n≤N) :
    (paths E N hn).mixingSteps (N^2) N=steps N := by
  rw [FiniteChains.CanonicalPaths.mixingSteps,FiniteChains.CanonicalPaths.scale]
  have hp : 0<(length N+1)*(8*(N+1)^2)*(traffic N+1) := by positivity
  rw [max_eq_right (by omega)]
  unfold steps
  ring

theorem row_event_error {n : ℕ} (E : MonotoneEndpoints n) (π : E.Permutations) (N k : ℕ)
    (hn : n≤N) (hk : k≤N) (A : E.Permutations → Prop) :
    |coinProbability ((1+(Nat.size n+Nat.size n))*steps N)
      (fun r => A (runCoins (MonotoneSwitch.step E (Nat.size n)) (steps N) π r))-
      (Fintype.card {x : E.Permutations // A x}:ℚ)/Fintype.card E.Permutations|≤1/(2^k:ℚ) := by
  let s := (inverseEquiv E).symm π
  letI : Nonempty (ColumnState E) := ⟨s⟩
  have hc : Fintype.card (ColumnState E)≤2^(N^2) :=
    (card_columnStates_le E).trans (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hn 2))
  have hh := runCoins_event_error (columnStep E (Nat.size n)) (columnStep_involutive E _)
    (columnStep_lazy E _) (paths E N hn) (N^2) N hc s (fun x => A (inverseEquiv E x))
  have ht := paths_steps E N hn
  rw [ht] at hh
  simp_rw [inverse_run] at hh
  have he : Fintype.card {x : ColumnState E // A (inverseEquiv E x)}=Fintype.card {x : E.Permutations // A x} :=
    Fintype.card_congr (Equiv.subtypeEquivOfSubtype (inverseEquiv E))
  rw [he,Fintype.card_congr (inverseEquiv E)] at hh
  have hs : inverseEquiv E s=π := (inverseEquiv E).apply_symm_apply π
  rw [hs] at hh
  refine hh.trans ?_
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_right₀ (by norm_num) hk

end HiddenCircuits.Approximation.SamplerRuntime.Budget
