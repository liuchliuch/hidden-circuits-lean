import HiddenCircuits.Approximation.CanonicalPaths.GeneralCycleRoute
import HiddenCircuits.Approximation.CanonicalPaths.ComponentCorrespondence

/-! A nontrivial actual union component admits the bounded cycle route, with
its enumeration and its maximum-row starting point both constructed. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
open LocalRoutes
variable {n : ℕ}

theorem restricted_component_route (E : MonotoneEndpoints n)
    (P Q : State (fun col row => Allowed E row col)) (active : Fin n)
    (hne : P.val active≠Q.val active) :
    ∃l<8*(componentPeriod P.val Q.val active)*(componentPeriod P.val Q.val active)+4,
      MarkedRoute Finset.univ
        (fun z => HasCompanion (restrictedSource P.val Q.val active E P.property)
          (restrictedTarget P.val Q.val active E Q.property) z 6)
        (restrictedSource P.val Q.val active E P.property)
        (restrictedTarget P.val Q.val active E Q.property) l := by
  obtain ⟨l,hl,hr⟩ := general_single_cycle_route
    (componentPresentation P.val Q.val active E P.property Q.property)
    (componentPeriod_gt_one P.val Q.val active hne)
  exact ⟨l,hl,by simpa only [componentPresentation_source,componentPresentation_target] using hr⟩

end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
