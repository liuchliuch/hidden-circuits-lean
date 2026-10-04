import HiddenCircuits.Approximation.SamplerRuntime.CoordinateSampler
import HiddenCircuits.GraphReduction.Runtime.StrictIntegerMembership
import HiddenCircuits.Approximation.SelfReduction.MatchingStates

/-! Native strict integer geometry. Scaling coordinates by two and using the
positive denominator2r−1 preserves every strict boundary, including radius1.
The empty and nonpositive-radius total-extension conventions remain separate. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerGeometry
open Complexity GraphReduction

def representation (G : GraphInput) (R : StrictIntegerRepresentation G) : UnitIntegerRepresentation G where
  denominator:=2*R.radius-1
  positive:=by have h:=R.positive;omega
  left i:=2*R.coordinate i
  adjacency i j:=by
    rw [R.adjacency,GraphReduction.Runtime.CoordinateGraph.integer_intervals _ _ _ (by have h:=R.positive;omega)]
    apply and_congr_right
    intro _
    rw [abs_lt]
    omega
lemma quasimonotone (G : GraphInput) (R : StrictIntegerRepresentation G) : Quasimonotone G.2.graph :=
  CoordinateSampler.quasimonotone G (representation G R)
lemma empty_count (G : GraphInput) (hG:G.1=0) : perfectMatchingCount G.2.graph=1 := by
  rcases G with ⟨n,G⟩
  change n=0 at hG
  subst n
  exact SelfReduction.perfectMatchingCount_empty_vertices G.graph
lemma raw_empty_count (xs : BitString) (hn:(LooseWordList.words (GraphReduction.Runtime.StrictInteger.data xs)).length=0) :
    strictIntegerProblem xs=1 := by
  rw [strictIntegerProblem_exact]
  exact empty_count (GraphReduction.Runtime.StrictInteger.graphInput xs) hn
end HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerGeometry
