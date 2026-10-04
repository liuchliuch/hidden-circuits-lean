import HiddenCircuits.Approximation.FiniteChains.Mixing

/-! Event-form consequences of the proved total-variation bound. -/
namespace HiddenCircuits.Approximation.FiniteChains
open scoped BigOperators
variable {α : Type*} [Fintype α]

noncomputable def eventMass (μ : α → ℝ) (E : α → Prop) : ℝ := by
  classical
  exact ∑ x, if E x then μ x else 0

/-- Equal-mass finite measures satisfy the usual event characterization of
half the L1 distance. No nonnegativity assumption is needed for this lemma. -/
theorem event_error_le_totalVariation (μ ν : α → ℝ)
    (hmass : ∑ x, μ x = ∑ x, ν x) (E : α → Prop) :
    |eventMass μ E-eventMass ν E| ≤ totalVariation μ ν := by
  classical
  let d : α → ℝ := fun x => μ x-ν x
  let a := ∑ x, if E x then d x else 0
  let b := ∑ x, if E x then 0 else d x
  have hsum : a+b=0 := by
    dsimp [a,b]
    rw [← Finset.sum_add_distrib]
    have he : (fun x => (if E x then d x else 0)+(if E x then 0 else d x)) = d := by
      funext x; split_ifs <;> simp
    rw [he]
    dsimp [d]
    rw [Finset.sum_sub_distrib,hmass,sub_self]
  have ha := Finset.abs_sum_le_sum_abs (fun x : α => if E x then d x else 0) Finset.univ
  have hb := Finset.abs_sum_le_sum_abs (fun x : α => if E x then 0 else d x) Finset.univ
  have hab : (∑ x, |if E x then d x else 0|) +
      (∑ x, |if E x then 0 else d x|) = ∑ x, |d x| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _; split_ifs <;> simp
  have hba : |b|=|a| := by
    have he : b = -a := by linarith
    rw [he,abs_neg]
  change |a| ≤ _ at ha
  change |b| ≤ _ at hb
  rw [hba] at hb
  have hevent : eventMass μ E-eventMass ν E=a := by
    unfold eventMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _; dsimp [d]; split_ifs <;> simp
  rw [hevent]
  unfold totalVariation
  change |a| ≤ (1:ℝ)/2 * ∑ x, |d x|
  linarith

namespace CanonicalPaths
variable [Nonempty α] {P : LazyChain α} {K L Q : ℕ} (C : CanonicalPaths P K L Q)

/-- The directly usable all-events sampling conclusion. -/
theorem event_error_le_dyadic (B k : ℕ) (hcard : Fintype.card α ≤ 2^B)
    (s : α) (E : α → Prop) :
    |eventMass (P.law (C.mixingSteps B k) s) E-eventMass P.uniform E| ≤ ((1:ℝ)/2)^k :=
  (event_error_le_totalVariation _ _ (by simp) E).trans (C.totalVariation_le_dyadic B k hcard s)

end CanonicalPaths
end HiddenCircuits.Approximation.FiniteChains
