import HiddenCircuits.Approximation.CanonicalPaths.CycleMiddleRoute
import HiddenCircuits.Approximation.CanonicalPaths.CycleBoundaryAssembly

/-! Complete single-cycle switch route, including both actual boundary repairs. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
open LocalRoutes
variable {n : ℕ} {E : MonotoneEndpoints n}

theorem single_cycle_marked_route (D : CyclePresentation E) (hn : 1<n)
    (hmax : (D.rows ⟨0,by omega⟩).val=n-1) :
    ∃l<8*n*n+4,MarkedRoute Finset.univ (fun z => HasCompanion D.source D.target z 6)
      D.source D.target l := by
  obtain ⟨z₀,z₁,⟨S,hS,h₀⟩,⟨T,hT,h₁⟩,l,hl,hr⟩ := cycle_middle_route D hn hmax
  exact connect_small_endpoints E D.source D.target z₀ z₁ S T hS hT h₀ h₁ hl hr

end HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
