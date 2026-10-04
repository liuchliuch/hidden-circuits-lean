import HiddenCircuits.GraphReduction.NaturalOrderedClasses
import HiddenCircuits.GraphReduction.Runtime.CliqueGraphHardness
import HiddenCircuits.GraphReduction.IntervalOrder
import HiddenCircuits.GraphReduction.RealUnitIntervals

/-! Exact counting on natural superclass promises. The reductions are the same
actual finite programs already verified for monotone and unit-interval queries;
only the independently proved class inclusions change the accepted oracle promise. -/
namespace HiddenCircuits.GraphReduction
open Complexity

/-- Enlarging a promised class preserves hardness and the common #P extension. -/
theorem ClassMatchingSharpPComplete.of_imp {P Q : GraphInput → Prop}
    (hP : ClassMatchingSharpPComplete P) (hPQ : ∀ G, P G → Q G) :
    ClassMatchingSharpPComplete Q := by
  refine ⟨⟨GraphInput.perfectMatchingProblem,
    GraphVerifier.MatchingRuntime.perfectMatching_sharpP,classMatchingOracle_full Q⟩,?_⟩
  intro g hg
  exact hP.2 g (fun G hG => hg G (hPQ G hG))

/-- #P-completeness for bipartite permutation graphs follows using genuine diagrams. -/
theorem bipartitePermutation_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => BipartitePermutationGraph G.2.graph) :=
  monotone_matching_sharpPComplete.of_imp (fun _ h => h.bipartitePermutation)

theorem biconvex_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => BiconvexGraph G.2.graph) :=
  monotone_matching_sharpPComplete.of_imp (fun _ h => h.biconvex)

theorem convex_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => ConvexGraph G.2.graph) :=
  biconvex_matching_sharpPComplete.of_imp (fun _ h => h.convex)

/-- The ordinary permutation class, without chordality or bipartiteness promises. -/
theorem permutation_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => PermutationGraph G.2.graph) :=
  bipartitePermutation_matching_sharpPComplete.of_imp (fun _ h => h.2)

/-- The rational closed-interval class, with arbitrary lengths and coincident endpoints. -/
def IntervalGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (Interval.Representation G)

def UnitInterval.Representation.toInterval {V : Type*} {G : SimpleGraph V}
    (r : UnitInterval.Representation G) : Interval.Representation G where
  left := r.left
  right v := r.left v+r.length
  ordered v := by linarith [r.positive]
  adjacency := r.adjacency

theorem UnitIntervalGraph.interval {V : Type} {G : SimpleGraph V}
    (hG : UnitIntervalGraph G) : IntervalGraph G :=
  ⟨hG.some.toInterval⟩

/-- Unit-interval queries already establish #P-completeness for general interval graphs. -/
theorem interval_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => IntervalGraph G.2.graph) :=
  unit_matching_sharpPComplete.of_imp (fun _ h => h.interval)

namespace RealInterval
/-- Actual closed intervals of the real line; arbitrary lengths, including singletons. -/
structure Representation {V : Type*} (G : SimpleGraph V) where
  left : V → ℝ
  right : V → ℝ
  ordered : ∀ v, left v ≤ right v
  adjacency : ∀ x y, G.Adj x y ↔ x ≠ y ∧
    (Set.Icc (left x) (right x) ∩ Set.Icc (left y) (right y)).Nonempty
end RealInterval

/-- The unrestricted real interval graph class on the original vertex labels. -/
def RealIntervalGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (RealInterval.Representation G)

noncomputable def Interval.Representation.toReal {V : Type*} {G : SimpleGraph V}
    (r : Interval.Representation G) : RealInterval.Representation G where
  left v := (r.left v : ℝ)
  right v := (r.right v : ℝ)
  ordered v := by exact_mod_cast r.ordered v
  adjacency x y := by
    rw [r.adjacency]
    apply and_congr_right
    intro _
    rw [UnitInterval.icc_overlap (r.ordered x) (r.ordered y),
      RealUnitInterval.icc_overlap (by exact_mod_cast r.ordered x) (by exact_mod_cast r.ordered y)]
    norm_cast

theorem IntervalGraph.realInterval {V : Type*} {G : SimpleGraph V}
    (hG : IntervalGraph G) : RealIntervalGraph G := ⟨hG.some.toReal⟩

/-- The real-coordinate interpretation requires no rationalization premise for hardness. -/
theorem realInterval_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => RealIntervalGraph G.2.graph) :=
  interval_matching_sharpPComplete.of_imp (fun _ h => h.realInterval)

end HiddenCircuits.GraphReduction
