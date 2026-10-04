import HiddenCircuits.DH.CographLexSlices

/-! The two-sweep module envelope invariant. Extra vertices in the normal slice
are universal to the recursive module; extra vertices in its complement slice
are independent. These properties are ordinary graph adjacency statements. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma GraphModule.inter {M S : Set V} (hM : GraphModule G M) (hS : GraphModule G S) :
    GraphModule G (M∩S) := by
  intro u hu v hv x hx
  by_cases hxM : x∈M
  · exact hS u hu.2 v hv.2 x (fun hxS => hx ⟨hxM,hxS⟩)
  · exact hM u hu.1 v hv.1 x hxM

/-- Restrict a pivot profile class to the current recursive module. -/
def relativePivotCell (G : SimpleGraph V) (M : Set V) (r x : V) : Set V :=
  M∩pivotCell G r x

lemma P4Free.relativePivotCell_module (hG : P4Free G) {M : Set V}
    (hM : GraphModule G M) (r x : V) : GraphModule G (relativePivotCell G M r x) :=
  hM.inter (hG.pivotCell_module r x)

def JoinEnvelope (G : SimpleGraph V) (M S : Set V) : Prop :=
  M⊆S ∧ ∀z∈S, z∉M → ∀a∈M, G.Adj a z

def UnionEnvelope (G : SimpleGraph V) (M S : Set V) : Prop :=
  M⊆S ∧ ∀z∈S, z∉M → ∀a∈M, ¬G.Adj a z

lemma JoinEnvelope.refl (M : Set V) : JoinEnvelope G M M := ⟨Set.Subset.rfl,by tauto⟩
lemma UnionEnvelope.refl (M : Set V) : UnionEnvelope G M M := ⟨Set.Subset.rfl,by tauto⟩

lemma JoinEnvelope.compl {M S : Set V} (h : JoinEnvelope G M S) : UnionEnvelope Gᶜ M S := by
  refine ⟨h.1,?_⟩
  intro z hz hzM a ha he
  exact ((G.compl_adj _ _).mp he).2 (h.2 z hz hzM a ha)

lemma UnionEnvelope.compl {M S : Set V} (h : UnionEnvelope G M S) : JoinEnvelope Gᶜ M S := by
  refine ⟨h.1,?_⟩
  intro z hz hzM a ha
  exact (G.compl_adj _ _).mpr ⟨fun he => hzM (he ▸ ha),h.2 z hz hzM a ha⟩

/-- Before the first vertex of a module is selected, the entire module lies in
its equal-prefix-profile slice. -/
lemma GraphModule.subset_profileSlice {M : Set V} (hM : GraphModule G M)
    (past : List V) {x : V} (hx : x∈M) (hfresh : ∀y∈M, y∉past) :
    M⊆profileSlice G past x := by
  intro y hy
  refine ⟨hfresh y hy,?_⟩
  intro z hz
  have hzM : z∉M := fun hm => hfresh z hm hz
  simpa only [G.adj_comm] using hM y hy x hx z hzM

/-- Equal-profile slices can only refine earlier slices. -/
lemma profileSlice_subset_earlier {past before : List V} (hp : past⊆before)
    {r x : V} (hx : x∈profileSlice G past r) :
    profileSlice G before x ⊆ profileSlice G past r := by
  intro y hy
  exact ⟨fun h => hy.1 (hp h),fun z hz => (hy.2 z (hp hz)).trans (hx.2 z hz)⟩

/-- Every descendant nonneighbor slice stays inside its local pivot profile
class, even after some vertices of that class have already been selected. -/
theorem profileSlice_subset_relativePivotCell {M S : Set V}
    (hM : GraphModule G M) (henv : JoinEnvelope G M S) {r x : V}
    (hrM : r∈M) (hxM : x∈M) (hx : x∈nonneighbors G r)
    (past : List V) (hr : r∈past)
    (hneighbors : ∀z∈M, G.Adj r z → z∈past)
    (hsub : profileSlice G past x ⊆ S) :
    profileSlice G past x ⊆ relativePivotCell G M r x := by
  intro y hy
  have hyr : y≠r := fun he => hy.1 (he ▸ hr)
  have hry : ¬G.Adj r y := fun he => hx.2 ((hy.2 r hr).mp he)
  have hyM : y∈M := by
    by_contra hyout
    exact hry (henv.2 y (hsub hy) hyout r hrM)
  refine ⟨hyM,⟨hyr,hry⟩,?_⟩
  ext z
  change (G.Adj r z ∧ G.Adj y z) ↔ (G.Adj r z ∧ G.Adj x z)
  by_cases hzM : z∈M
  · by_cases hrz : G.Adj r z
    · have he := hy.2 z (hneighbors z hzM hrz)
      exact and_congr Iff.rfl (by simpa only [G.adj_comm] using he)
    · simp [hrz]
  · exact and_congr Iff.rfl (hM y hyM x hxM z hzM)

/-- A recorded descendant slice of a universal envelope is exactly its local
nonneighbor profile class once all local neighbors have been visited. -/
theorem P4Free.profileSlice_eq_relativePivotCell (hG : P4Free G) {M S : Set V}
    (hM : GraphModule G M) (henv : JoinEnvelope G M S) {r x : V}
    (hrM : r∈M) (hxM : x∈M) (hx : x∈nonneighbors G r)
    (past : List V) (hr : r∈past)
    (hneighbors : ∀z∈M, G.Adj r z → z∈past)
    (hfresh : ∀y∈relativePivotCell G M r x, y∉past)
    (hsub : profileSlice G past x ⊆ S) :
    profileSlice G past x = relativePivotCell G M r x := by
  ext y
  constructor
  · intro hy
    have hyr : y≠r := fun he => hy.1 (he ▸ hr)
    have hry : ¬G.Adj r y := fun he => hx.2 ((hy.2 r hr).mp he)
    have hyM : y∈M := by
      by_contra hyout
      exact hry (henv.2 y (hsub hy) hyout r hrM)
    refine ⟨hyM,⟨hyr,hry⟩,?_⟩
    ext z
    change (G.Adj r z ∧ G.Adj y z) ↔ (G.Adj r z ∧ G.Adj x z)
    by_cases hzM : z∈M
    · by_cases hrz : G.Adj r z
      · have he := hy.2 z (hneighbors z hzM hrz)
        exact and_congr Iff.rfl (by simpa only [G.adj_comm] using he)
      · simp [hrz]
    · exact and_congr Iff.rfl (hM y hyM x hxM z hzM)
  · intro hy
    exact (hG.relativePivotCell_module hM r x).subset_profileSlice past
      ⟨hxM,mem_pivotCell_self hx⟩ hfresh hy

/-- Normal nonneighbor children preserve the independent envelope in the other
sweep. Its extra vertices cannot mix edges with the recursive child. -/
theorem P4Free.unionEnvelope_relative_child (hG : P4Free G) {M S T : Set V}
    (henv : UnionEnvelope G M S) {r x : V}
    (hchild : relativePivotCell G M r x ⊆ T) (hsub : T⊆S)
    (hrout : r∉T) (hn : ∀z∈T, ¬G.Adj r z) :
    UnionEnvelope G (relativePivotCell G M r x) T := by
  refine ⟨hchild,?_⟩
  intro z hz hzC a ha
  by_cases hzM : z∈M
  · intro haz
    have hzN : z∈nonneighbors G r := ⟨fun he => hrout (he ▸ hz),hn z hz⟩
    have hp := hG.pivotProfile_eq_of_edge ha.2.1 hzN haz
    exact hzC ⟨hzM,hzN,hp.symm.trans ha.2.2⟩
  · exact henv.2 z (hsub hz) hzM a ha.1

/-- The previous root belongs to the later prefix, so a nonneighbor child's
whole opposite-sweep profile slice stays nonadjacent to that root. -/
lemma profileSlice_nonneighbor {past : List V} {r x : V} (hr : r∈past)
    (hx : ¬G.Adj r x) : ∀z∈profileSlice G past x, ¬G.Adj r z := by
  intro z hz he
  exact hx ((hz.2 r hr).mp he)

/-- A module's first selected vertex is the minimum original tie rank in either
sweep. In particular the complement sweep uses the same recursive module roots. -/
theorem GraphModule.sweep_first_eq [DecidableRel G.Adj] {M : Set V}
    (hM : GraphModule G M) (s : Bool) (tie : List V) (rank : V → ℕ)
    (hrank : tie.Pairwise (fun u v => rank u < rank v)) (hinj : Function.Injective rank)
    (hall : ∀v∈M, v∈tie) (before : List (LexBFSModel.Event V))
    (e : LexBFSModel.Event V) (after : List (LexBFSModel.Event V))
    (he : LexBFSModel.sweep (fun a b => decide (G.Adj a b)) s tie = before++e::after)
    (heM : e.vertex∈M) (hfresh : ∀b∈before, b.vertex∉M)
    {first : V} (hfirst : first∈M) (hmin : ∀v∈M, rank first ≤ rank v) :
    e.vertex = first := by
  have ht := LexBFSModel.sweep_ties (fun a b => decide (G.Adj a b)) s rank tie hrank
  rw [he] at ht
  apply ht.first_group_eq heM hfresh _ _ hfirst hmin hinj
  · intro v hv
    have hp := LexBFSModel.sweep_perm (fun a b => decide (G.Adj a b)) s tie
    rw [he] at hp
    exact hp.mem_iff.mpr (hall v hv)
  · intro z hz u hu v hv
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    apply (prefers_graph_equal s b.vertex u v).mpr
    simpa only [G.adj_comm] using hM u hu v hv b.vertex (hfresh b hb)

end HiddenCircuits.DH
