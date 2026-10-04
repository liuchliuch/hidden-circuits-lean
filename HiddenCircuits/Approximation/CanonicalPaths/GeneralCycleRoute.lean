import HiddenCircuits.Approximation.CanonicalPaths.CycleBoundaryRoutes
import HiddenCircuits.Approximation.CanonicalPaths.CycleRotation

/-! The maximum-row start is constructed rather than assumed. -/
namespace HiddenCircuits.Approximation.CanonicalPaths
open LocalRoutes
variable {n : ℕ} {E : MonotoneEndpoints n}

theorem general_single_cycle_route (D : CyclePresentation E) (hn : 1<n) :
    ∃l<8*n*n+4,MarkedRoute Finset.univ (fun z => HasCompanion D.source D.target z 6)
      D.source D.target l := by
  obtain ⟨D',hp,hq,hmax⟩ := D.exists_maximum_start (by omega)
  obtain ⟨l,hl,hr⟩ := CycleMountain.single_cycle_marked_route D' hn hmax
  exact ⟨l,hl,by simpa only [hp,hq] using hr⟩

end HiddenCircuits.Approximation.CanonicalPaths
