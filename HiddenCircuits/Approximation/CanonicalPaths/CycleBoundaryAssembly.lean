import HiddenCircuits.Approximation.CanonicalPaths.LiftedRoutes
import HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation

/-! The at-most-two-column mountain boundary corrections are actual confined
switch paths, with complementary matching witnesses at every vertex. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
variable {n : ℕ} (E : MonotoneEndpoints n)

theorem connect_small_endpoints (p q z₀ z₁ : State (fun col row => Allowed E row col))
    (S T : Finset (Fin n)) (hS : S.card≤2) (hT : T.card≤2)
    (hz₀ : ∀i,i∉S → z₀.val i=p.val i) (hz₁ : ∀i,i∉T → z₁.val i=q.val i)
    {l B : ℕ} (hl : l<B)
    (middle : MarkedRoute Finset.univ (fun z => HasCompanion p q z 6) z₀ z₁ l) :
    ∃k<B+4,MarkedRoute Finset.univ (fun z => HasCompanion p q z 6) p q k := by
  obtain ⟨a,ha,hr₀⟩ := route_of_agree_outside (endpoint_ordered E) p z₀ S (fun i hi => (hz₀ i hi).symm)
  obtain ⟨b,hb,hr₁⟩ := route_of_agree_outside (endpoint_ordered E) q z₁ T (fun i hi => (hz₁ i hi).symm)
  have hm₀ : MarkedRoute Finset.univ (fun z => HasCompanion p q z 6) p z₀ a := by
    have hm := hr₀.mark_companion (HasCompanion.initial p q 0) hS
    exact hm.mono (Finset.subset_univ _) (fun z h => h.mono (by decide))
  have hm₁ : MarkedRoute Finset.univ (fun z => HasCompanion p q z 6) q z₁ b := by
    have hm := hr₁.mark_companion (HasCompanion.final p q 0) hT
    exact hm.mono (Finset.subset_univ _) (fun z h => h.mono (by decide))
  exact ⟨a+l+b,by omega,(hm₀.append middle).append hm₁.reverse⟩

end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
