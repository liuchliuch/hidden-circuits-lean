import HiddenCircuits.Approximation.CanonicalPaths.CompanionCoverage
import HiddenCircuits.Approximation.CanonicalPaths.MarkedWalks

/-! Fresh interpolation between nearby focus configurations, with six repairs. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
open LocalRoutes
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n} (D : CyclePresentation E)

theorem neighboring_route (a b c d : Fin n) (hab : a < b) (hcd : c < d)
    (hov : D.FocusOverlap a b) (hov' : D.FocusOverlap c d)
    (hac : a.val ≤ c.val+1) (hca : c.val ≤ a.val+1)
    (hbd : b.val ≤ d.val+1) (hdb : d.val ≤ b.val+1) :
    ∃k ≤ 4,MarkedRoute Finset.univ (fun Z => HasCompanion D.source D.target Z 6)
      (D.primary a b hab hov) (D.primary c d hcd hov') k := by
  let t := D.primaryCut a b hab
  let u := D.primaryCut c d hcd
  have ht := D.primaryCut_bounds a b hab
  have hu := D.primaryCut_bounds c d hcd
  have htu : t.val ≤ u.val+2 := by dsimp [t,u]; omega
  have hut : u.val ≤ t.val+2 := by dsimp [t,u]; omega
  let T := blockChangeSupport a t c u
  have hT : T.card ≤ 4 := blockChangeSupport_card a t c u htu hut
  have hout : ∀i,i∉T → blockRotation a t i=blockRotation c u i :=
    fun i hi => blockRotation_agree_outside a t c u (D.primaryCut_ge a b hab) (D.primaryCut_ge c d hcd) hac hca i hi
  have route : ∃k ≤ T.card,Route (T.image D.columns) (D.primary a b hab hov) (D.primary c d hcd hov') k :=
    D.state_route _ _ _ _ T hout
  obtain ⟨k,hk,hr⟩ := route
  have hImage : (T.image D.columns).card ≤ 4 := (Finset.card_image_le).trans hT
  have hm := hr.mark_companion (D.primary_hasCompanion a b hab hov) hImage
  exact ⟨k,hk.trans hT,hm.mono (Finset.subset_univ _) (fun _ h => h)⟩

end HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
