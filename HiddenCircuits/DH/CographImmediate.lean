import HiddenCircuits.DH.CographEnvelopes

/-! The profile-class characterization of immediate nonpreferred slice children. -/
namespace HiddenCircuits.DH
open SimpleGraph LexBFSModel
variable {V : Type*} {G : SimpleGraph V}

/-- No slice opened strictly between the parent root and this child contains the
child. This is the graph-profile form of the endpoint stack's latest-parent test. -/
def NoIntermediateSlice (G : SimpleGraph V) (past : List V) (r : V) (middle : List V) (x : V) : Prop :=
  ∀before y after, middle=before++y::after → x∉profileSlice G (past++r::before) y

/-- The earliest vertex of an untouched local profile class has no intermediate
containing slice after the parent pivot. -/
theorem P4Free.profileCell_no_intermediate (hG : P4Free G) {M S : Set V}
    (hM : GraphModule G M) (henv : JoinEnvelope G M S) {r x : V}
    (hrM : r∈M) (hxM : x∈M) (hx : x∈nonneighbors G r)
    (past middle : List V) (hrmiddle : r∉middle) (hroot : S=profileSlice G past r)
    (hmiddle : ∀y∈middle, y∈S)
    (hfresh : ∀y∈relativePivotCell G M r x, y∉middle)
    (hneighbors : ∀before y after, middle=before++y::after → ¬G.Adj r y →
      ∀z∈M, G.Adj r z → z∈past++r::before) :
    NoIntermediateSlice G past r middle x := by
  intro before y after he hcontains
  have hyS := hmiddle y (by rw [he]; simp)
  have hrpast : r∈past++r::before := by simp
  have hchild : profileSlice G (past++r::before) y ⊆ S := by
    rw [hroot] at hyS ⊢
    exact profileSlice_subset_earlier (fun _ h => List.mem_append_left _ h) hyS
  by_cases hry : G.Adj r y
  · exact hx.2 ((hcontains.2 r hrpast).mpr hry)
  · have hyM : y∈M := by
      by_contra hyout
      exact hry (henv.2 y hyS hyout r hrM)
    have hyr : y≠r := by
      intro heq
      subst y
      exact hrmiddle (by rw [he]; simp)
    have hyN : y∈nonneighbors G r := ⟨hyr,hry⟩
    have hxC := profileSlice_subset_relativePivotCell hM henv hrM hyM hyN
      (past++r::before) hrpast (hneighbors before y after he hry) hchild hcontains
    have hyC : y∈relativePivotCell G M r x := ⟨hyM,hyN,hxC.2.2.symm⟩
    exact hfresh y hyC (by rw [he]; simp)

lemma exists_first_mem_set (xs : List V) (C : Set V) (h : ∃x∈xs, x∈C) :
    ∃before x after, xs=before++x::after ∧ x∈C ∧ ∀y∈before, y∉C := by
  induction xs with
  | nil => simpa using h
  | cons x xs ih =>
    by_cases hx : x∈C
    · exact ⟨[],x,xs,rfl,hx,by simp⟩
    · have ht : ∃y∈xs, y∈C := by
        obtain ⟨y,hy,hyC⟩ := h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact False.elim (hx hyC)
        · exact ⟨y,hy,hyC⟩
      obtain ⟨before,y,after,he,hyC,hbefore⟩ := ih ht
      refine ⟨x::before,y,after,by simp [he],hyC,?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hbefore z hz

/-- A direct child cannot have an earlier vertex of its module between it and
the parent root, since that first vertex's slice would still contain the child. -/
lemma NoIntermediateSlice.fresh_module {C : Set V} (hC : GraphModule G C)
    {past middle : List V} {r x : V} (hx : x∈C) (hr : r∉C)
    (hpast : ∀y∈C, y∉past) (hno : NoIntermediateSlice G past r middle x) :
    ∀y∈C, y∉middle := by
  intro y hy hym
  obtain ⟨before,z,after,he,hz,hbefore⟩ := exists_first_mem_set middle C ⟨y,hym,hy⟩
  have hfresh : ∀a∈C, a∉past++r::before := by
    intro a ha ham
    rcases List.mem_append.mp ham with ham | ham
    · exact hpast a ha ham
    · rcases List.mem_cons.mp ham with rfl | ham
      · exact hr ha
      · exact hbefore a ham ha
  exact hno before z after he ((hC.subset_profileSlice _ hz hfresh) hx)

end HiddenCircuits.DH
