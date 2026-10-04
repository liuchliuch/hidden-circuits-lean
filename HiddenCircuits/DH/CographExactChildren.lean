import HiddenCircuits.DH.CographParentSemantics

/-! Exact local classification of normal nonpreferred slice children as first
vertices of pivot-profile classes, under the proved module-envelope invariant. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel SliceHeads
variable {V : Type*} {G : SimpleGraph V}

def EventParent (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) : Prop :=
  let p : Frame V := ⟨root.vertex,past.length,past.length+root.sliceSize⟩
  let c : Frame V := ⟨child.vertex,past.length+1+middle.length,past.length+1+middle.length+child.sliceSize⟩
  IsParent (framesFrom 0 past++p::framesFrom (past.length+1) middle) c (some p)

lemma sweep_middle_subset_rootSlice [DecidableRel G.Adj] (s : Bool) (tie : List V)
    (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) s tie = past++root::middle++child::after)
    (hc : child.vertex∈profileSlice G (past.map Event.vertex) root.vertex) :
    ∀v∈middle.map Event.vertex, v∈profileSlice G (past.map Event.vertex) root.vertex := by
  have hbound := (sweep_interval_contains_iff s tie htie hall past root middle child after he).mpr hc
  have hsize : (root.vertex::middle.map Event.vertex).length≤root.sliceSize := by
    simp only [List.length_cons,List.length_map]
    omega
  have hs := sweep_event_slice_graph s tie htie hall past root (middle++child::after)
    (by simpa [List.append_assoc] using he)
  intro v hv
  rw [←hs]
  simp only [Set.mem_setOf_eq,List.map_cons,List.map_append]
  change v∈((root.vertex::middle.map Event.vertex)++child.vertex::after.map Event.vertex).take root.sliceSize
  rw [List.take_append,List.take_of_length_le hsize]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ hv)

lemma NoIntermediateEvents.fresh_module {C : Set V} (hC : GraphModule G C)
    {past middle : List (Event V)} {r x : Event V} (hx : x.vertex∈C) (hr : r.vertex∉C)
    (hpast : ∀y∈C, y∉past.map Event.vertex) (hno : NoIntermediateEvents G past r middle x) :
    ∀y∈C, y∉(past++r::middle).map Event.vertex := by
  intro y hy hm
  simp only [List.map_append,List.map_cons,List.mem_append,List.mem_cons] at hm
  rcases hm with hm | he | hm
  · exact hpast y hy hm
  · exact hr (he ▸ hy)
  · obtain ⟨e,hem,hey⟩ := List.mem_map.mp hm
    obtain ⟨before,z,after,he,hz,hbefore⟩ := exists_first_event_in_set middle C ⟨e,hem,hey ▸ hy⟩
    have hfresh : ∀a∈C, a∉(past++r::before).map Event.vertex := by
      intro a ha ham
      simp only [List.map_append,List.map_cons,List.mem_append,List.mem_cons] at ham
      rcases ham with ham | har | ham
      · exact hpast a ha ham
      · exact hr (har ▸ ha)
      · obtain ⟨b,hb,hba⟩ := List.mem_map.mp ham
        exact hbefore b hb (hba ▸ ha)
    exact hno before z after he ((hC.subset_profileSlice _ hz hfresh) hx)

/-- An actual normal-sweep nonpreferred edge is present precisely for the first
unvisited vertex of its local pivot-profile class. This identifies the compact
stack/bucket output with the graph modules used by cotree extraction. -/
theorem P4Free.normal_child_iff [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) true tie = past++root::middle++child::after)
    {M : Set V} (hM : GraphModule G M) (hrM : root.vertex∈M)
    (henv : JoinEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex))
    (hn : ¬G.Adj root.vertex child.vertex) :
    EventParent past root middle child ↔ child.vertex∈M ∧
      ∀v∈relativePivotCell G M root.vertex child.vertex,
        v∉(past++root::middle).map Event.vertex := by
  have hparent := sweep_parent_iff true tie htie hall past root middle child after he
  change EventParent past root middle child ↔ _ at hparent
  rw [hparent]
  constructor
  · rintro ⟨hc,hno⟩
    have hcM : child.vertex∈M := by
      by_contra hout
      exact hn (henv.2 child.vertex hc hout root.vertex hrM)
    have hcr : child.vertex≠root.vertex := by
      intro hEq
      have hp := sweep_perm (fun a b => decide (G.Adj a b)) true tie
      rw [he] at hp
      have hnd := hp.nodup_iff.mpr htie
      have hd : ((past.map Event.vertex)++root.vertex::(middle.map Event.vertex++child.vertex::after.map Event.vertex)).Nodup := by
        simpa [List.map_append,List.append_assoc] using hnd
      exact (List.nodup_cons.mp (List.nodup_append.mp hd).2.1).1 (by simp [hEq])
    have hxC : child.vertex∈relativePivotCell G M root.vertex child.vertex := ⟨hcM,⟨hcr,hn⟩,rfl⟩
    refine ⟨hcM,hno.fresh_module (hG.relativePivotCell_module hM _ _) hxC ?_ ?_⟩
    · intro h; exact h.2.1.1 rfl
    · intro y hy; exact (henv.1 hy.1).1
  · rintro ⟨hcM,hfresh⟩
    have hcr : child.vertex≠root.vertex := by
      intro heq
      have hp := sweep_perm (fun a b => decide (G.Adj a b)) true tie
      rw [he] at hp
      have hnd := hp.nodup_iff.mpr htie
      have hd : ((past.map Event.vertex)++root.vertex::(middle.map Event.vertex++child.vertex::after.map Event.vertex)).Nodup := by
        simpa [List.map_append,List.append_assoc] using hnd
      exact (List.nodup_cons.mp (List.nodup_append.mp hd).2.1).1 (by simp [heq])
    have hrootC := henv.1 hcM
    refine ⟨hrootC,?_⟩
    intro before e rest hm hcontains
    have heM : e.vertex∈profileSlice G (past.map Event.vertex) root.vertex :=
      sweep_middle_subset_rootSlice true tie htie hall past root middle child after he hrootC
        e.vertex (by rw [hm]; simp)
    have hrpast : root.vertex∈(past++root::before).map Event.vertex := by simp
    by_cases hre : G.Adj root.vertex e.vertex
    · exact hn ((hcontains.2 root.vertex hrpast).mpr hre)
    · have hemod : e.vertex∈M := by
        by_contra hout
        exact hre (henv.2 e.vertex heM hout root.vertex hrM)
      have her : e.vertex≠root.vertex := by
        intro heq
        have hp := sweep_perm (fun a b => decide (G.Adj a b)) true tie
        rw [he,hm] at hp
        have hnd := hp.nodup_iff.mpr htie
        have hd : (past.map Event.vertex++root.vertex::
            (before.map Event.vertex++e.vertex::rest.map Event.vertex++child.vertex::after.map Event.vertex)).Nodup := by
          simpa [List.map_append,List.append_assoc] using hnd
        exact (List.nodup_cons.mp (List.nodup_append.mp hd).2.1).1 (by simp [heq])
      have hneigh : ∀z∈M, G.Adj root.vertex z → z∈(past++root::before).map Event.vertex := by
        intro z hz hzadj
        have he' : sweep (fun a b => decide (G.Adj a b)) true tie =
            past++root::before++e::(rest++child::after) := by simp [he,hm,List.append_assoc]
        have hs := sweep_event_slice_graph (G := G) true tie htie hall past root (before++e::rest++child::after)
          (by simp [he,hm,List.append_assoc])
        apply sweep_slice_preferred_before (fun a b => decide (G.Adj a b)) true tie past root before e
          (rest++child::after) he'
        · have hh := hs ▸ heM; simpa [List.append_assoc] using hh
        · simp [prefers,hre]
        · have hh := hs ▸ henv.1 hz; simpa [List.append_assoc] using hh
        · simp [prefers,hzadj]
      have hsub : profileSlice G ((past++root::before).map Event.vertex) e.vertex ⊆
          profileSlice G (past.map Event.vertex) root.vertex :=
        profileSlice_subset_earlier (by intro a ha; simp [ha]) heM
      have hxCell := profileSlice_subset_relativePivotCell hM henv hrM hemod ⟨her,hre⟩
        _ hrpast hneigh hsub hcontains
      have heCell : e.vertex∈relativePivotCell G M root.vertex child.vertex :=
        ⟨hemod,⟨her,hre⟩,hxCell.2.2.symm⟩
      exact hfresh e.vertex heCell (by simp [hm,List.map_append])

lemma profileSlice_subset_compl (past : List V) {x : V} (hx : x∉past) :
    profileSlice G past x ⊆ profileSlice Gᶜ past x := by
  intro y hy
  refine ⟨hy.1,?_⟩
  intro z hz
  have hzx : z≠x := fun he => hx (he ▸ hz)
  have hzy : z≠y := fun he => hy.1 (he ▸ hz)
  have h := hy.2 z hz
  constructor
  · intro he
    exact (G.compl_adj _ _).mpr ⟨hzx,fun hzx => ((G.compl_adj _ _).mp he).2 (h.mpr hzx)⟩
  · intro he
    exact (G.compl_adj _ _).mpr ⟨hzy,fun hzy => ((G.compl_adj _ _).mp he).2 (h.mp hzy)⟩

lemma profileSlice_compl (past : List V) {x : V} (hx : x∉past) :
    profileSlice Gᶜ past x = profileSlice G past x := by
  apply Set.Subset.antisymm
  · simpa using (profileSlice_subset_compl (G := Gᶜ) past hx)
  · exact profileSlice_subset_compl past hx

/-- The opposite sweep has the symmetric exact child-class characterization,
using only ordinary original adjacency rows through the complement adapter. -/
theorem P4Free.complement_child_iff [DecidableRel G.Adj] (hG : P4Free G)
    (tie : List V) (htie : tie.Nodup) (hall : ∀v, v∈tie)
    (past : List (Event V)) (root : Event V) (middle : List (Event V))
    (child : Event V) (after : List (Event V))
    (he : sweep (fun a b => decide (G.Adj a b)) false tie = past++root::middle++child::after)
    {M : Set V} (hM : GraphModule G M) (hrM : root.vertex∈M)
    (henv : UnionEnvelope G M (profileSlice G (past.map Event.vertex) root.vertex))
    (hadj : G.Adj root.vertex child.vertex) :
    EventParent past root middle child ↔ child.vertex∈M ∧
      ∀v∈relativePivotCell Gᶜ M root.vertex child.vertex,
        v∉(past++root::middle).map Event.vertex := by
  classical
  have he' : sweep (fun a b => decide (Gᶜ.Adj a b)) true tie = past++root::middle++child::after := by
    rw [←sweep_graph_complement G tie htie]
    exact he
  have hrootFresh : root.vertex∉past.map Event.vertex := by
    have hp := sweep_perm (fun a b => decide (G.Adj a b)) false tie
    rw [he] at hp
    have hn := hp.nodup_iff.mpr htie
    have hn' : (past.map Event.vertex++root.vertex::(middle.map Event.vertex++child.vertex::after.map Event.vertex)).Nodup := by
      simpa [List.map_append,List.append_assoc] using hn
    intro hm
    exact (List.nodup_append.mp hn').2.2 root.vertex hm root.vertex List.mem_cons_self rfl
  apply hG.compl.normal_child_iff tie htie hall past root middle child after he' hM.compl hrM
  · rw [profileSlice_compl _ hrootFresh]
    exact henv.compl
  · intro he
    exact ((G.compl_adj _ _).mp he).2 hadj

end HiddenCircuits.DH
