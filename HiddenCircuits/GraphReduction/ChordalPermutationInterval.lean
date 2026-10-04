import HiddenCircuits.GraphReduction.PermutationDownsets
import HiddenCircuits.GraphReduction.OrderedSuperclassHardness

/-! Full-graph equivalence of chordal permutation graphs and interval permutation
graphs, obtained from the actual two-coordinate order and literal intervals. -/
namespace HiddenCircuits.GraphReduction

namespace PermutationDiagram
variable {V : Type*} [Fintype V] (D : PermutationDiagram V)

def natIntervalRepresentation (hG : Chordal D.graph) : Interval.NatRepresentation D.graph :=
  Interval.ofNestedDownsets D.below D.graph D.below_irrefl (D.nestedDownsets hG) D.adj_iff_incomparable

def intervalRepresentation (hG : Chordal D.graph) : Interval.Representation D.graph :=
  (D.natIntervalRepresentation hG).toRational

/-- Integer endpoints already suffice for every finite chordal permutation graph. -/
theorem chordal_iff_intervalRepresentation :
    Chordal D.graph ↔ Nonempty (Interval.Representation D.graph) :=
  ⟨fun h => ⟨D.intervalRepresentation h⟩,fun h => h.some.chordal⟩
end PermutationDiagram

/-- Both witnesses represent the same labeled graph. -/
def IntervalPermutationGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  IntervalGraph G ∧ PermutationGraph G

/-- The real-coordinate version uses unrestricted closed intervals. -/
def RealIntervalPermutationGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  RealIntervalGraph G ∧ PermutationGraph G

/-- The induced-cycle argument applies to real endpoints without rationalization. -/
theorem RealInterval.Representation.chordal {V : Type*} {G : SimpleGraph V}
    (r : RealInterval.Representation G) : Chordal G := by
  intro n hn
  letI : NeZero n := ⟨by omega⟩
  constructor
  intro e
  obtain ⟨i,hmin⟩ := Finite.exists_min (fun j : Fin n => r.right (e j))
  obtain ⟨a,b,hia,hib,hab,hnab⟩ := cycle_neighbors_nonadjacent hn i
  obtain ⟨_,u,⟨_,hui⟩,⟨hua,_⟩⟩ := (r.adjacency (e i) (e a)).mp (e.map_adj_iff.mpr hia)
  obtain ⟨_,v,⟨_,hvi⟩,⟨hvb,_⟩⟩ := (r.adjacency (e i) (e b)).mp (e.map_adj_iff.mpr hib)
  apply hnab
  apply e.map_adj_iff.mp
  apply (r.adjacency (e a) (e b)).mpr
  exact ⟨fun h => hab (e.injective h),r.right (e i),
    ⟨hua.trans hui,hmin a⟩,⟨hvb.trans hvi,hmin b⟩⟩

/-- The natural-class equality, including empty graphs and isolated vertices. -/
theorem chordalPermutationGraph_iff_intervalPermutationGraph {V : Type} [Finite V]
    (G : SimpleGraph V) : ChordalPermutationGraph G ↔ IntervalPermutationGraph G := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  constructor
  · rintro ⟨hc,D,hD⟩
    refine ⟨?_,D,hD⟩
    rw [←hD] at hc ⊢
    exact ⟨D.intervalRepresentation hc⟩
  · rintro ⟨hi,hp⟩
    exact ⟨hi.some.chordal,hp⟩

theorem chordalPermutationGraph_iff_realIntervalPermutationGraph {V : Type} [Finite V]
    (G : SimpleGraph V) : ChordalPermutationGraph G ↔ RealIntervalPermutationGraph G := by
  constructor
  · intro h
    have hI := (chordalPermutationGraph_iff_intervalPermutationGraph G).mp h
    exact ⟨hI.1.realInterval,hI.2⟩
  · rintro ⟨hi,hp⟩
    exact ⟨hi.some.chordal,hp⟩

/-- Exact counting remains complete on the actual intersection of both classes. -/
theorem intervalPermutation_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => IntervalPermutationGraph G.2.graph) :=
  private_matching_sharpPComplete.of_imp
    (fun G h => (chordalPermutationGraph_iff_intervalPermutationGraph G.2.graph).mp h)

theorem realIntervalPermutation_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => RealIntervalPermutationGraph G.2.graph) :=
  private_matching_sharpPComplete.of_imp
    (fun G h => (chordalPermutationGraph_iff_realIntervalPermutationGraph G.2.graph).mp h)

end HiddenCircuits.GraphReduction
