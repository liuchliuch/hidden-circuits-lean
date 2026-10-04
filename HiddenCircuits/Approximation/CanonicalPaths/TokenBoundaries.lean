import HiddenCircuits.Approximation.CanonicalPaths.CompanionCoverage

/-! Fresh two-column agreement of extreme token configurations with the endpoints. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
open LocalRoutes
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n} (D : CyclePresentation E)

private theorem restore_agreement (a b : Fin n) (P Q : State (fun col row => Allowed E row col))
    (h : ∀i,i≠a → i≠b → P.val (D.columns i)=Q.val (D.columns i)) :
    ∀x,x∉({D.columns a,D.columns b} : Finset (Fin n)) → P.val x=Q.val x := by
  intro x hx
  let i := D.columns.symm x
  have hi : D.columns i=x := D.columns.apply_symm_apply x
  have hia : i≠a := by intro h; exact hx (by simp [← hi,h])
  have hib : i≠b := by intro h; exact hx (by simp [← hi,h])
  simpa only [hi] using h i hia hib

theorem primary_boundary_source (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b)
    (ha : a.val=0) (hb : b.val=n-1) :
    ∃S : Finset (Fin n),S.card ≤ 2 ∧ ∀i,i∉S → (D.primary a b hab hov).val i=D.source.val i := by
  refine ⟨{D.columns a,D.columns b},?_,?_⟩
  · by_cases h : D.columns a=D.columns b <;> simp [h]
  · apply restore_agreement D a b
    intro i hia hib
    have hia' : i.val≠a.val := fun h => hia (Fin.ext h)
    have hib' : i.val≠b.val := fun h => hib (Fin.ext h)
    have hi := i.isLt
    have hc := D.primaryCut_bounds a b hab
    have hin : a < i ∧ i ≤ D.primaryCut a b hab := by
      change a.val < i.val ∧ i.val ≤ _
      omega
    rw [D.primary_apply,blockRotation_apply _ _ _ (D.primaryCut_ge a b hab)]
    simp only [if_neg hia,if_pos hin,source,state_apply,Equiv.refl_apply]

theorem primary_boundary_target (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b)
    (hba : b.val=a.val+1) :
    ∃S : Finset (Fin n),S.card ≤ 2 ∧ ∀i,i∉S → (D.primary a b hab hov).val i=D.target.val i := by
  refine ⟨{D.columns a,D.columns b},?_,?_⟩
  · by_cases h : D.columns a=D.columns b <;> simp [h]
  · apply restore_agreement D a b
    intro i hia hib
    have hib' : i.val≠b.val := fun h => hib (Fin.ext h)
    have hc := D.primaryCut_bounds a b hab
    have hout : ¬(a < i ∧ i ≤ D.primaryCut a b hab) := by
      change ¬(a.val < i.val ∧ i.val ≤ _)
      omega
    rw [D.primary_apply,blockRotation_apply _ _ _ (D.primaryCut_ge a b hab)]
    simp only [if_neg hia,if_neg hout,target,state_apply]

end HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
