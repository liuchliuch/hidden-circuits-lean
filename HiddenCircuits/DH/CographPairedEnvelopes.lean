import HiddenCircuits.DH.CographExactChildren

/-! Propagation of the paired module-envelope invariant to recursive profile cells. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel
variable {V : Type*} {G : SimpleGraph V}

lemma sweep_neighbors_before [DecidableRel G.Adj] (tie : List V)
    (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) true tie=past++root::middle++child::after)
    (hc : child.vertex∈profileSlice G (past.map Event.vertex) root.vertex)
    (hn : ¬G.Adj root.vertex child.vertex) :
    ∀z∈profileSlice G (past.map Event.vertex) root.vertex, G.Adj root.vertex z →
      z∈(past++root::middle).map Event.vertex := by
  have hs := sweep_event_slice_graph (G := G) true tie htie hall past root (middle++child::after)
    (by simpa [List.append_assoc] using he)
  intro z hz hzadj
  apply sweep_slice_preferred_before (fun a b => decide (G.Adj a b)) true tie past root middle child after he
  · simpa only [Set.mem_setOf_eq,List.append_assoc] using (Set.ext_iff.mp hs child.vertex).mpr hc
  · simp [prefers,hn]
  · simpa only [Set.mem_setOf_eq,List.append_assoc] using (Set.ext_iff.mp hs z).mpr hz
  · simp [prefers,hzadj]

/-- Recursive normal profile cells inherit an exact normal slice and an
independent envelope in the opposite sweep. The opposite root agreement is
provided by the already proved module/tie lemma, not by recomputing a sweep. -/
theorem P4Free.normal_envelopes_child [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) true tie=past++root::middle++child::after)
    {M : Set V} (hM : GraphModule G M) (hrM : root.vertex∈M) (hcM : child.vertex∈M)
    (hx : child.vertex∈nonneighbors G root.vertex)
    (hnormal : JoinEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex))
    (otherPast otherMiddle : List V)
    (hother : UnionEnvelope G M (profileSlice G otherPast root.vertex))
    (hfresh : ∀v∈relativePivotCell G M root.vertex child.vertex,
      v∉(past++root::middle).map Event.vertex)
    (hfreshOther : ∀v∈relativePivotCell G M root.vertex child.vertex,
      v∉otherPast++root.vertex::otherMiddle) :
    let C := relativePivotCell G M root.vertex child.vertex
    GraphModule G C ∧
      JoinEnvelope G C (profileSlice G ((past++root::middle).map Event.vertex) child.vertex) ∧
      UnionEnvelope G C (profileSlice G (otherPast++root.vertex::otherMiddle) child.vertex) := by
  dsimp only
  let C := relativePivotCell G M root.vertex child.vertex
  have hC : GraphModule G C := hG.relativePivotCell_module hM _ _
  have hcC : child.vertex∈C := ⟨hcM,mem_pivotCell_self hx⟩
  have hrPrefix : root.vertex∈(past++root::middle).map Event.vertex := by simp
  have hneighbors : ∀z∈M, G.Adj root.vertex z → z∈(past++root::middle).map Event.vertex := by
    intro z hz hzadj
    exact sweep_neighbors_before tie htie hall past root middle child after he (hnormal.1 hcM) hx.2
      z (hnormal.1 hz) hzadj
  have hsub : profileSlice G ((past++root::middle).map Event.vertex) child.vertex ⊆
      profileSlice G (past.map Event.vertex) root.vertex :=
    profileSlice_subset_earlier (by intro a ha; simp [ha]) (hnormal.1 hcM)
  have hnormalEq : profileSlice G ((past++root::middle).map Event.vertex) child.vertex=C :=
    hG.profileSlice_eq_relativePivotCell hM hnormal hrM hcM hx _ hrPrefix hneighbors hfresh hsub
  refine ⟨hC,?_,?_⟩
  · rw [hnormalEq]
    exact JoinEnvelope.refl C
  · apply hG.unionEnvelope_relative_child hother
    · exact hC.subset_profileSlice _ hcC hfreshOther
    · exact profileSlice_subset_earlier (fun _ h => List.mem_append_left _ h) (hother.1 hcM)
    · intro h; exact h.1 (by simp)
    · exact profileSlice_nonneighbor (by simp) hx.2

/-- Complementary profile-cell children propagate the symmetric pair of
independent/universal envelopes without materializing a complement graph. -/
theorem P4Free.complement_envelopes_child [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) false tie=past++root::middle++child::after)
    {M : Set V} (hM : GraphModule G M) (hrM : root.vertex∈M) (hcM : child.vertex∈M)
    (hadj : G.Adj root.vertex child.vertex)
    (hcomplement : UnionEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex))
    (otherPast otherMiddle : List V)
    (hother : JoinEnvelope G M (profileSlice G otherPast root.vertex))
    (hfresh : ∀v∈relativePivotCell Gᶜ M root.vertex child.vertex,
      v∉(past++root::middle).map Event.vertex)
    (hfreshOther : ∀v∈relativePivotCell Gᶜ M root.vertex child.vertex,
      v∉otherPast++root.vertex::otherMiddle) :
    let C := relativePivotCell Gᶜ M root.vertex child.vertex
    GraphModule G C ∧
      UnionEnvelope G C (profileSlice G ((past++root::middle).map Event.vertex) child.vertex) ∧
      JoinEnvelope G C (profileSlice G (otherPast++root.vertex::otherMiddle) child.vertex) := by
  classical
  dsimp only
  have he' : sweep (fun a b => decide (Gᶜ.Adj a b)) true tie=past++root::middle++child::after := by
    rw [←sweep_graph_complement G tie htie]
    exact he
  have hx : child.vertex∈nonneighbors Gᶜ root.vertex := by rw [nonneighbors_compl]; exact hadj
  have hnormal : JoinEnvelope Gᶜ M (profileSlice Gᶜ (past.map Event.vertex) root.vertex) := by
    rw [profileSlice_compl _ (hcomplement.1 hrM).1]
    exact hcomplement.compl
  have hother' : UnionEnvelope Gᶜ M (profileSlice Gᶜ otherPast root.vertex) := by
    rw [profileSlice_compl _ (hother.1 hrM).1]
    exact hother.compl
  obtain ⟨hC,hn,ho⟩ := hG.compl.normal_envelopes_child tie htie hall past root middle child after he'
    hM.compl hrM hcM hx hnormal otherPast otherMiddle hother' hfresh hfreshOther
  have hcC : child.vertex∈relativePivotCell Gᶜ M root.vertex child.vertex :=
    ⟨hcM,mem_pivotCell_self hx⟩
  have hnf := hfresh child.vertex hcC
  have hof := hfreshOther child.vertex hcC
  refine ⟨graphModule_compl_iff.mp hC,?_,?_⟩
  · have h := hn.compl
    simpa only [compl_compl,profileSlice_compl _ hnf] using h
  · have h := ho.compl
    simpa only [compl_compl,profileSlice_compl _ hof] using h

end HiddenCircuits.DH
