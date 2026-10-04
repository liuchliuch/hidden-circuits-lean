import HiddenCircuits.Approximation.SelfReduction.Frequency
import HiddenCircuits.Approximation.SelfReduction.Adaptive
import HiddenCircuits.Approximation.SelfReduction.HeavyBranch

/-! Exact count fibers and approximate empirical branch selection. The sampler
is used as supplied; no count is queried by `branchFrequencies` or `selectedBranch`. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

/-- Exact self-reduction data. The recurrence is mathematical semantics, not an
oracle operation; executable selection below never reads `count`. -/
structure CountReduction (S : Type*) (b : ℕ) where
  count : S → ℕ
  rank : S → ℕ
  child : S → Fin (b+1) → S
  leaf_count : ∀ s, rank s=0 → count s ≤ 1
  child_rank : ∀ s i, 0 < rank s → rank (child s i)+1=rank s
  recurrence : ∀ s, 0 < rank s → count s = ∑ i, count (child s i)

namespace CountReduction
variable {S : Type*} {b : ℕ} (R : CountReduction S b)

def branchProbability (s : S) (i : Fin (b+1)) : ℚ := (R.count (R.child s i) : ℚ)/R.count s

theorem branchProbability_sum (s : S) (hr : 0 < R.rank s) (hc : 0 < R.count s) :
    ∑ i, R.branchProbability s i = 1 := by
  unfold branchProbability
  rw [← Finset.sum_div, ← Nat.cast_sum, ← R.recurrence s hr]
  have hn : (R.count s : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  exact div_self hn

end CountReduction

/-- Amplified observed frequencies for every possible partner. Samples may be
shared across partners; the union-bound analysis does not assume their independence. -/
def branchFrequencies {S α : Type*} (b T k : ℕ) (sampler : S → α → Option (Fin (b+1)))
    (s : S) (r : Fin (2*(k+1)) → Fin (batchSize T) → α) (i : Fin (b+1)) : ℚ :=
  amplifiedFrequency (fun a => sampler s a=some i) T k r

/-- An actual maximum scan on empirical values. -/
def selectedBranch {S α : Type*} (b T k : ℕ) (sampler : S → α → Option (Fin (b+1)))
    (s : S) (r : Fin (2*(k+1)) → Fin (batchSize T) → α) : Fin (b+1) :=
  chooseMax b (branchFrequencies b T k sampler s r)

/-- Each branch's near-uniform sampling guarantee yields simultaneous estimation
accuracy, with explicit union-bound loss equal to the number of branches. -/
theorem branchFrequencies_failure {S α : Type*} [Fintype α] [Nonempty α]
    (b T k : ℕ) (hT : 0 < T) (sampler : S → α → Option (Fin (b+1)))
    (s : S) (p : Fin (b+1) → ℚ)
    (hbias : ∀ i, |probability (fun a => sampler s a=some i)-p i| ≤ 1/(T : ℚ)) :
    probability (fun r => ∃ i, 6/(T : ℚ) < |branchFrequencies b T k sampler s r i-p i|) ≤
      (b+1 : ℚ)/(2^(k+1) : ℚ) := by
  classical
  calc
    _ ≤ ∑ i, probability (fun r => 6/(T : ℚ) < |branchFrequencies b T k sampler s r i-p i|) :=
      probability_exists _
    _ ≤ ∑ _ : Fin (b+1), 1/(2^(k+1) : ℚ) := by
      apply Finset.sum_le_sum
      intro i _
      exact amplifiedFrequency_failure (fun a => sampler s a=some i) T hT k (p i) (hbias i)
    _ = _ := by simp [div_eq_mul_inv]

/-- Accurate empirical branch selection provides every needed local count and
inverse-ratio condition, including positivity of the chosen child. -/
theorem selectedBranch_correct {S α : Type*} (b T k : ℕ) (hT : 0 < T)
    (R : CountReduction S b) (sampler : S → α → Option (Fin (b+1)))
    (s : S) (hr : 0 < R.rank s) (hc : 0 < R.count s)
    (r : Fin (2*(k+1)) → Fin (batchSize T) → α)
    (hsize : (24 : ℚ)*(b+1) ≤ T)
    (hgood : ∀ i, |branchFrequencies b T k sampler s r i-R.branchProbability s i| ≤ 6/(T : ℚ)) :
    let j := selectedBranch b T k sampler s r
    0 < R.count (R.child s j) ∧ 0 < branchFrequencies b T k sampler s r j ∧
      |R.branchProbability s j/branchFrequencies b T k sampler s r j-1| ≤
        12*(b+1 : ℚ)/T := by
  let q := branchFrequencies b T k sampler s r
  let j := selectedBranch b T k sampler s r
  have hT' : (0 : ℚ) < T := by exact_mod_cast hT
  have hb : (0 : ℚ) < b+1 := by positivity
  have hδ : 6/(T : ℚ) ≤ 1/(4*(b+1 : ℚ)) := by
    apply (div_le_div_iff₀ hT' (by positivity)).2
    nlinarith
  have hh := chooseMax_heavy b (R.branchProbability s) q (R.branchProbability_sum s hr hc)
    (6/(T : ℚ)) hδ hgood
  have hp : (0 : ℚ) < R.branchProbability s j := (by positivity : (0 : ℚ)<1/(2*(b+1 : ℚ))).trans_le hh.1
  have hq : (0 : ℚ) < q j := (by positivity : (0 : ℚ)<1/(2*(b+1 : ℚ))).trans_le hh.2
  have hchild : 0 < R.count (R.child s j) := by
    by_contra hz
    have he : R.count (R.child s j)=0 := by omega
    simp [CountReduction.branchProbability, he] at hp
  refine ⟨hchild,hq,?_⟩
  have he := inverse_ratio_error (R.branchProbability s j) (q j) (6/(T : ℚ))
    (1/(2*(b+1 : ℚ))) (by positivity) hh.2 (hgood j)
  convert he using 1 <;> field_simp <;> ring

end HiddenCircuits.Approximation.SelfReduction
