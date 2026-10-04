import HiddenCircuits.DH.CographSlices

/-! Rooted cograph decomposition via extremal pivot profiles. The semantic blocks
are derived from adjacency, without assuming a cotree or a recognition certificate. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- A block which can replace the pivot by a union or join once its interior has
been assembled. All edges to the rest are exactly the pivot's original edges. -/
structure RootTwinBlock (G : SimpleGraph V) (r : V) (joined : Bool) (S : Set V) : Prop where
  root_out : r∉S
  root_adj : ∀ x∈S, (G.Adj r x ↔ joined = true)
  external : ∀ x∈S, ∀ z∉S, z≠r → (G.Adj x z ↔ G.Adj r z)

lemma RootTwinBlock.module {r : V} {b : Bool} {S : Set V} (h : RootTwinBlock G r b S) :
    GraphModule G S := by
  intro u hu v hv x hx
  by_cases hxr : x=r
  · subst x
    exact (by simpa only [G.adj_comm] using (h.root_adj u hu).trans (h.root_adj v hv).symm)
  · exact (h.external u hu x hx hxr).trans (h.external v hv x hx hxr).symm

lemma RootTwinBlock.compl {r : V} {b : Bool} {S : Set V} (h : RootTwinBlock G r b S) :
    RootTwinBlock Gᶜ r (!b) S where
  root_out := h.root_out
  root_adj x hx := by
    have hrx : r≠x := fun he => h.root_out (he ▸ hx)
    rw [G.compl_adj]
    have ha := h.root_adj x hx
    cases b <;> simp_all
  external x hx z hz hzr := by
    have hxz : x≠z := fun he => hz (he ▸ hx)
    have hrz : r≠z := hzr.symm
    rw [G.compl_adj,G.compl_adj]
    have he := h.external x hx z hz hzr
    exact ⟨fun hh => ⟨hrz,fun ha => hh.2 (he.mpr ha)⟩,
      fun hh => ⟨hxz,fun ha => hh.2 (he.mp ha)⟩⟩

/-- A full nonneighbor profile is precisely a false-twin block of the pivot. -/
theorem P4Free.full_pivotCell_rootBlock (hG : P4Free G) {r x : V}
    (hx : x∈nonneighbors G r) (hfull : pivotProfile G r x = G.neighborSet r) :
    RootTwinBlock G r false (pivotCell G r x) where
  root_out h := h.1.1 rfl
  root_adj a ha := iff_of_false ha.1.2 Bool.false_ne_true
  external a ha z hz hzr := by
    by_cases hrz : G.Adj r z
    · have hzP : z∈pivotProfile G r a := by rw [ha.2,hfull]; exact hrz
      exact iff_of_true hzP.2 hrz
    · have hzN : z∈nonneighbors G r := ⟨hzr,hrz⟩
      have haz : ¬G.Adj a z := by
        intro he
        exact hz ⟨hzN,(hG.pivotProfile_eq_of_edge ha.1 hzN he).symm.trans ha.2⟩
      exact iff_of_false haz hrz

/-- Maximal normal and complement profiles decide which type of root block is
innermost using a single original-graph adjacency query. -/
theorem maximal_profiles_choose_inner {r x y : V}
    (hx : x∈nonneighbors G r) (hy : y∈nonneighbors Gᶜ r)
    (hxmax : ∀ z∈nonneighbors G r, pivotProfile G r z ⊆ pivotProfile G r x)
    (hymax : ∀ z∈nonneighbors Gᶜ r, pivotProfile Gᶜ r z ⊆ pivotProfile Gᶜ r y) :
    (G.Adj x y → pivotProfile G r x = G.neighborSet r) ∧
      (¬G.Adj x y → pivotProfile Gᶜ r y = Gᶜ.neighborSet r) := by
  constructor
  · intro hxy
    apply Set.Subset.antisymm (fun _ h => h.1)
    intro z hrz
    refine ⟨hrz,?_⟩
    by_contra hxz
    have hz : z∈nonneighbors Gᶜ r := by rw [nonneighbors_compl]; exact hrz
    have hxP : x∈pivotProfile Gᶜ r z :=
      ⟨(G.compl_adj _ _).mpr ⟨hx.1.symm,hx.2⟩,
        (G.compl_adj _ _).mpr ⟨fun he => hx.2 (he ▸ hrz),fun he => hxz he.symm⟩⟩
    exact ((G.compl_adj _ _).mp (hymax z hz hxP).2).2 hxy.symm
  · intro hxy
    apply Set.Subset.antisymm (fun _ h => h.1)
    intro z hrz
    obtain ⟨hrzne,hrzn⟩ := (G.compl_adj _ _).mp hrz
    have hz : z∈nonneighbors G r := ⟨hrzne.symm,hrzn⟩
    have hry : G.Adj r y := by simpa only [nonneighbors_compl,mem_neighborSet] using hy
    have hzy : ¬G.Adj z y := fun he => hxy (hxmax z hz ⟨hry,he⟩).2
    refine ⟨hrz,(G.compl_adj _ _).mpr ⟨?_,fun he => hzy he.symm⟩⟩
    intro he
    exact hrzn (he ▸ hry)

/-- Both branches of the executable first-head adjacency test have their exact
union/join block semantics. -/
theorem P4Free.maximal_profiles_rootBlocks (hG : P4Free G) {r x y : V}
    (hx : x∈nonneighbors G r) (hy : y∈nonneighbors Gᶜ r)
    (hxmax : ∀ z∈nonneighbors G r, pivotProfile G r z ⊆ pivotProfile G r x)
    (hymax : ∀ z∈nonneighbors Gᶜ r, pivotProfile Gᶜ r z ⊆ pivotProfile Gᶜ r y) :
    (G.Adj x y → RootTwinBlock G r false (pivotCell G r x)) ∧
      (¬G.Adj x y → RootTwinBlock G r true (pivotCell Gᶜ r y)) := by
  have hm := maximal_profiles_choose_inner hx hy hxmax hymax
  constructor
  · intro h; exact hG.full_pivotCell_rootBlock hx (hm.1 h)
  · intro h
    have he := (hG.compl.full_pivotCell_rootBlock hy (hm.2 h)).compl
    simpa using he

end HiddenCircuits.DH
