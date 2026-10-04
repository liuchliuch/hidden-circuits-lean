import HiddenCircuits.Approximation.CanonicalPaths.TokenConfiguration
import HiddenCircuits.Approximation.CanonicalPaths.CompanionRoutes

/-! Fresh two-column reconstruction profile for the actual token companion. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
open LocalRoutes
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n} (D : CyclePresentation E)

theorem index_pair (a b : Fin n) (hab : a < b) (i : Fin n) (hia : i≠a) (hib : i≠b) :
    ({blockRotation a (D.primaryCut a b hab) i,Fin.cycleIcc (D.companionCut a b) b i} : Finset (Fin n))=
      {i,finRotate n i} := by
  have hp := D.primaryCut_bounds a b hab
  have hc := D.companionCut_bounds a b hab
  have hia' : i.val≠a.val := fun h => hia (Fin.ext h)
  have hib' : i.val≠b.val := fun h => hib (Fin.ext h)
  have hprimary : (a < i ∧ i ≤ D.primaryCut a b hab) ↔ (a < i ∧ i < b) := by
    change (a.val < i.val ∧ i.val ≤ _) ↔ (a.val < i.val ∧ i.val < b.val)
    omega
  have hcompanion : (D.companionCut a b ≤ i ∧ i < b) ↔ (a < i ∧ i < b) := by
    change (_ ≤ i.val ∧ i.val < b.val) ↔ (a.val < i.val ∧ i.val < b.val)
    omega
  rw [blockRotation_apply a _ i (D.primaryCut_ge a b hab),cycleIcc_apply _ b i (D.companionCut_le a b hab)]
  simp only [if_neg hia,if_neg hib,hprimary,hcompanion]
  split_ifs <;> simp [Finset.pair_comm]

theorem primary_hasCompanion (a b : Fin n) (hab : a < b) (hov : D.FocusOverlap a b) :
    HasCompanion D.source D.target (D.primary a b hab hov) 2 := by
  let S : Finset (Fin n) := {D.columns a,D.columns b}
  have hS : S.card ≤ 2 := by
    by_cases h : D.columns a=D.columns b <;> simp [S,h]
  refine ⟨D.companion a b hab hov,S,hS,?_⟩
  intro x hx
  let i := D.columns.symm x
  have hi : D.columns i=x := D.columns.apply_symm_apply x
  have hia : i≠a := by intro h; exact hx (by simp [S,← hi,h])
  have hib : i≠b := by intro h; exact hx (by simp [S,← hi,h])
  have hp := congrArg (fun T : Finset (Fin n) => T.image D.rows) (D.index_pair a b hab i hia hib)
  simp only [Finset.image_insert,Finset.image_singleton] at hp
  rw [← hi,D.primary_apply,D.companion_apply]
  simpa only [source,target,state_apply,Equiv.refl_apply] using hp

end HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
