import HiddenCircuits.Approximation.SelfReduction.MatchingCounting

/-! Natural tallies and comparisons for empirical selection.
Rational arithmetic is confined to the final binary product loops. -/
namespace HiddenCircuits.Approximation.SelfReduction

/-- Maximum scanning depends only on pairwise comparison results. -/
theorem chooseMax_order_congr {β γ : Type*} [LinearOrder β] [LinearOrder γ]
    (n : ℕ) (p : Fin (n+1) → β) (q : Fin (n+1) → γ)
    (h : ∀ i j, p i ≤ p j ↔ q i ≤ q j) : chooseMax n p = chooseMax n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := ih (fun i => p i.succ) (fun i => q i.succ) (fun i j => h i.succ j.succ)
    simp only [chooseMax, ht]
    by_cases hp : p 0 ≤ p (chooseMax n (fun i => q i.succ)).succ
    · simp only [if_pos hp, if_pos ((h _ _).mp hp)]
    · have hq : ¬q 0 ≤ q (chooseMax n (fun i => q i.succ)).succ := fun hh => hp ((h _ _).mpr hh)
      simp only [if_neg hp, if_neg hq]

theorem chooseMax_natural_div (n M : ℕ) (hM : 0 < M) (c : Fin (n+1) → ℕ) :
    chooseMax n (fun i => (c i : ℚ)/M) = chooseMax n c := by
  apply chooseMax_order_congr
  intro i j
  rw [div_le_div_iff_of_pos_right (by exact_mod_cast hM : (0 : ℚ)<M)]
  exact_mod_cast Iff.rfl

/-- An integer-only neighborhood test. -/
def naturalCluster (n : ℕ) (c : Fin (n+1) → ℕ) (radius : ℕ) (i : Fin (n+1)) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun j => c j ≤ c i+radius ∧ c i ≤ c j+radius

theorem natural_interval_test (a b radius M : ℕ) (hM : 0 < M) :
    |(a : ℚ)/M-(b : ℚ)/M| ≤ (radius : ℚ)/M ↔ a ≤ b+radius ∧ b ≤ a+radius := by
  have hM' : (0 : ℚ)<M := by exact_mod_cast hM
  rw [← sub_div, abs_div, abs_of_pos hM', div_le_div_iff_of_pos_right hM', abs_le]
  constructor
  · intro h
    constructor
    · have hh : (a : ℚ) ≤ (b : ℚ)+radius := by linarith
      exact_mod_cast hh
    · have hh : (b : ℚ) ≤ (a : ℚ)+radius := by linarith
      exact_mod_cast hh
  · rintro ⟨ha,hb⟩
    have ha' : (a : ℚ) ≤ (b : ℚ)+radius := by exact_mod_cast ha
    have hb' : (b : ℚ) ≤ (a : ℚ)+radius := by exact_mod_cast hb
    constructor <;> linarith

/-- Because every batch has the same denominator 2T², the robust selector's
rational interval test is exactly a natural comparison at radius 8T. -/
theorem frequency_cluster_eq (n T : ℕ) (hT : 0 < T) (c : Fin (n+1) → ℕ) (i : Fin (n+1)) :
    cluster n (fun j => (c j : ℚ)/batchSize T) (2/(T : ℚ)) i =
      naturalCluster n c (8*T) i := by
  have hM : 0 < batchSize T := by unfold batchSize; positivity
  have ht : 2*(2/(T : ℚ)) = ((8*T : ℕ) : ℚ)/batchSize T := by
    have hT' : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
    unfold batchSize
    push_cast
    field_simp
    <;> ring
  ext j
  simp only [cluster, naturalCluster, Finset.mem_filter, Finset.mem_univ, true_and, ht]
  exact natural_interval_test _ _ _ _ hM

/-- Integer frequency tally for a single batch. -/
def eventCount {α : Type*} (n : ℕ) (E : α → Prop) [DecidablePred E] (r : Fin n → α) : ℕ :=
  (Finset.univ.filter fun i => E (r i)).card

def naturalAmplifiedCount {α : Type*} (E : α → Prop) [DecidablePred E] (T k : ℕ)
    (r : StageTape α T k) : ℕ :=
  let c : Fin (2*k+1+1) → ℕ := fun i => eventCount (batchSize T) E (r (Fin.cast (by omega) i))
  c (chooseMax (2*k+1) (fun i => (naturalCluster (2*k+1) c (8*T) i).card))

/-- The bounded-integer implementation returns exactly the same count as the
statistically analyzed rational formulation, on every tape. -/
theorem naturalAmplifiedCount_eq {α : Type*} (E : α → Prop) [DecidablePred E]
    (T k : ℕ) (hT : 0 < T) (r : StageTape α T k) :
    naturalAmplifiedCount E T k r = amplifiedCount E T k r := by
  unfold naturalAmplifiedCount amplifiedCount
  simp only [eventFrequency,eventCount]
  simp_rw [frequency_cluster_eq _ _ hT]

end HiddenCircuits.Approximation.SelfReduction
