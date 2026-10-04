import HiddenCircuits.GraphReduction.IntervalOrder
import HiddenCircuits.GraphReduction.LayeredChordal

/-! Closed interval graphs exclude all induced cycles of length at least four. -/
namespace HiddenCircuits.GraphReduction.Interval
variable {V : Type*} {G : SimpleGraph V}

lemma Representation.adjacency_bounds (r : Representation G) (x y : V) :
    G.Adj x y ↔ x ≠ y ∧ r.left x ≤ r.right y ∧ r.left y ≤ r.right x := by
  rw [r.adjacency]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z,⟨hxl,hxr⟩,⟨hyl,hyr⟩⟩
    exact ⟨hxl.trans hyr,hyl.trans hxr⟩
  · rintro ⟨hxy,hyx⟩
    refine ⟨max (r.left x) (r.left y), ?_⟩
    exact ⟨⟨le_max_left _ _,max_le (r.ordered x) hyx⟩,
      ⟨le_max_right _ _,max_le hxy (r.ordered y)⟩⟩

/-- A minimum-right-endpoint cycle vertex has adjacent cycle neighbors. -/
theorem Representation.chordal (r : Representation G) : Chordal G := by
  intro n hn
  letI : NeZero n := ⟨by omega⟩
  constructor
  intro e
  obtain ⟨i,hmin⟩ := Finite.exists_min (fun j : Fin n => r.right (e j))
  obtain ⟨a,b,hia,hib,hab,hnab⟩ := cycle_neighbors_nonadjacent hn i
  have ha := (r.adjacency_bounds (e i) (e a)).mp (e.map_adj_iff.mpr hia)
  have hb := (r.adjacency_bounds (e i) (e b)).mp (e.map_adj_iff.mpr hib)
  apply hnab
  apply e.map_adj_iff.mp
  apply (r.adjacency_bounds (e a) (e b)).mpr
  exact ⟨fun h => hab (e.injective h),ha.2.2.trans (hmin b),hb.2.2.trans (hmin a)⟩

end HiddenCircuits.GraphReduction.Interval
