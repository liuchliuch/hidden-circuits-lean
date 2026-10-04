import HiddenCircuits.DH.CographTree
import HiddenCircuits.DH.Preprocessing

/-! Semantic component modules used to identify cograph LexBFS subslices. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- The induced four-vertex path is self-complementary. -/
lemma P4Free.compl (hG : P4Free G) : P4Free Gᶜ := by
  refine ⟨fun p => ?_⟩
  have ha (i j : Fin 4) (hij : (pathGraph 4).Adj i j) : ¬G.Adj (p i) (p j) :=
    ((G.compl_adj _ _).mp (p.map_rel_iff.mpr hij)).2
  have hn (i j : Fin 4) (hne : i≠j) (hij : ¬(pathGraph 4).Adj i j) : G.Adj (p i) (p j) := by
    by_contra h
    exact hij (p.map_rel_iff.mp ((G.compl_adj _ _).mpr ⟨fun he => hne (p.injective he),h⟩))
  exact hG.no_path4 (p 2) (p 0) (p 3) (p 1)
    (hn 2 0 (by decide) (by simp [pathGraph_adj]))
    (hn 0 3 (by decide) (by simp [pathGraph_adj]))
    (hn 3 1 (by decide) (by simp [pathGraph_adj]))
    (ha 2 3 (by simp [pathGraph_adj]))
    (ha 2 1 (by simp [pathGraph_adj]))
    (ha 0 1 (by simp [pathGraph_adj]))

lemma GraphModule.compl {S : Set V} (hS : GraphModule G S) : GraphModule Gᶜ S := by
  intro u hu v hv x hx
  have hux : u≠x := fun he => hx (he ▸ hu)
  have hvx : v≠x := fun he => hx (he ▸ hv)
  rw [G.compl_adj,G.compl_adj]
  exact ⟨fun h => ⟨hvx,(not_congr (hS u hu v hv x hx)).mp h.2⟩,
    fun h => ⟨hux,(not_congr (hS u hu v hv x hx)).mpr h.2⟩⟩

lemma graphModule_compl_iff {S : Set V} : GraphModule Gᶜ S ↔ GraphModule G S := by
  constructor
  · intro h; simpa using h.compl
  · exact GraphModule.compl

/-- Modules of an induced module remain modules in the original graph. -/
lemma GraphModule.induce_lift {S : Set V} (hS : GraphModule G S) {T : Set S}
    (hT : GraphModule (G.induce S) T) : GraphModule G (Subtype.val '' T) := by
  rintro u ⟨u',hu',rfl⟩ v ⟨v',hv',rfl⟩ x hx
  by_cases hxS : x∈S
  · exact hT u' hu' v' hv' ⟨x,hxS⟩ (fun ht => hx ⟨⟨x,hxS⟩,ht,rfl⟩)
  · exact hS u'.val u'.property v'.val v'.property x hxS

/-- Uniform cuts between any two disjoint modules. -/
lemma GraphModule.cross_uniform {S T : Set V} (hS : GraphModule G S) (hT : GraphModule G T)
    (hd : Disjoint S T) {u v x y : V} (hu : u∈S) (hv : v∈S) (hx : x∈T) (hy : y∈T) :
    G.Adj u x ↔ G.Adj v y := by
  have hxS : x∉S := fun h => Set.disjoint_left.mp hd h hx
  have hvT : v∉T := fun h => Set.disjoint_left.mp hd hv h
  exact (hS u hu v hv x hxS).trans (by
    simpa only [G.adj_comm] using hT x hx y hy v hvT)

/-- All vertices other than the pivot which are not its neighbors. -/
def nonneighbors (G : SimpleGraph V) (r : V) : Set V := {x | x≠r ∧ ¬G.Adj r x}

/-- An edge inside the nonneighbor set cannot distinguish a neighbor of the pivot. -/
lemma P4Free.nonneighbor_edge_uniform (hG : P4Free G) {r x y z : V}
    (hx : x∈nonneighbors G r) (hy : y∈nonneighbors G r)
    (hxy : G.Adj x y) (hrz : G.Adj r z) : G.Adj x z ↔ G.Adj y z := by
  have forward {a b : V} (ha : a∈nonneighbors G r) (hb : b∈nonneighbors G r)
      (hab : G.Adj a b) (haz : G.Adj a z) : G.Adj b z := by
    by_contra hbz
    exact hG.no_path4 r z a b hrz haz.symm hab ha.2 hb.2 (fun h => hbz h.symm)
  exact ⟨forward hx hy hxy,forward hy hx hxy.symm⟩

lemma P4Free.nonneighbor_reachable_uniform (hG : P4Free G) {r z : V}
    (hrz : G.Adj r z) {x y : nonneighbors G r}
    (hr : (G.induce (nonneighbors G r)).Reachable x y) : G.Adj x.val z ↔ G.Adj y.val z := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    exact (hG.nonneighbor_edge_uniform a.property b.property h hrz).trans ih

/-- Each component outside the pivot's closed neighborhood is a genuine module
of the whole cograph, not merely of the nonneighbor induced graph. -/
theorem P4Free.nonneighbor_component_module (hG : P4Free G) (r : V)
    (C : (G.induce (nonneighbors G r)).ConnectedComponent) :
    GraphModule G (componentVertices (nonneighbors G r) C) := by
  intro u hu v hv x hx
  by_cases hxr : x=r
  · subst x
    have hu' := componentVertices_subset _ C hu
    have hv' := componentVertices_subset _ C hv
    exact iff_of_false (fun h => hu'.2 h.symm) (fun h => hv'.2 h.symm)
  · by_cases hrx : G.Adj r x
    · obtain ⟨u',hu',rfl⟩ := hu
      obtain ⟨v',hv',rfl⟩ := hv
      have hr := C.connected_toSimpleGraph.preconnected ⟨u',hu'⟩ ⟨v',hv'⟩
      exact hG.nonneighbor_reachable_uniform hrx (hr.map (Embedding.induce C.supp).toHom)
    · have hxN : x∈nonneighbors G r := ⟨hxr,hrx⟩
      exact iff_of_false (fun h => hx (componentVertices_closed _ C hu hxN h))
        (fun h => hx (componentVertices_closed _ C hv hxN h))

/-- Complement symmetry gives the other kind of cograph branch module. -/
theorem P4Free.neighbor_cocomponent_module (hG : P4Free G) (r : V)
    (C : (Gᶜ.induce (nonneighbors Gᶜ r)).ConnectedComponent) :
    GraphModule G (componentVertices (nonneighbors Gᶜ r) C) := by
  exact graphModule_compl_iff.mp (hG.compl.nonneighbor_component_module r C)

@[simp] lemma nonneighbors_compl (r : V) : nonneighbors Gᶜ r = G.neighborSet r := by
  ext x
  simp only [nonneighbors,Set.mem_setOf_eq,mem_neighborSet,G.compl_adj]
  constructor
  · rintro ⟨hx,hn⟩
    by_contra ha
    exact hn ⟨hx.symm,ha⟩
  · intro ha
    exact ⟨ha.ne.symm,fun h => h.2 ha⟩

/-- A pivot-relative external profile; unlike a finite table it is universe-polymorphic. -/
def pivotProfile (G : SimpleGraph V) (r x : V) : Set V := {z | G.Adj r z ∧ G.Adj x z}

/-- Nonneighbors with the same neighborhood in the pivot's neighbor set form one
maximal nonadjacent subslice. This definition says only equality of graph profiles. -/
def pivotCell (G : SimpleGraph V) (r x : V) : Set V :=
  {y | y∈nonneighbors G r ∧ pivotProfile G r y = pivotProfile G r x}

lemma mem_pivotCell_self {r x : V} (hx : x∈nonneighbors G r) : x∈pivotCell G r x := ⟨hx,rfl⟩

lemma P4Free.pivotProfiles_nested (hG : P4Free G) {r x y : V}
    (hx : x∈nonneighbors G r) (hy : y∈nonneighbors G r) :
    pivotProfile G r x ⊆ pivotProfile G r y ∨ pivotProfile G r y ⊆ pivotProfile G r x := by
  rcases hG.common_neighbors_nested hx.2 hy.2 with h | h
  · exact Or.inl (fun _ hz => ⟨hz.1,h _ hz.1 hz.2⟩)
  · exact Or.inr (fun _ hz => ⟨hz.1,h _ hz.1 hz.2⟩)

lemma P4Free.pivotProfile_eq_of_edge (hG : P4Free G) {r x y : V}
    (hx : x∈nonneighbors G r) (hy : y∈nonneighbors G r) (hxy : G.Adj x y) :
    pivotProfile G r x = pivotProfile G r y := by
  ext z
  change (G.Adj r z ∧ G.Adj x z) ↔ (G.Adj r z ∧ G.Adj y z)
  constructor
  · intro h; exact ⟨h.1,(hG.nonneighbor_edge_uniform hx hy hxy h.1).mp h.2⟩
  · intro h; exact ⟨h.1,(hG.nonneighbor_edge_uniform hx hy hxy h.1).mpr h.2⟩

/-- Equal-profile nonneighbors are modules even when the class is disconnected. -/
theorem P4Free.pivotCell_module (hG : P4Free G) (r x : V) : GraphModule G (pivotCell G r x) := by
  intro u hu v hv z hz
  have huv : pivotProfile G r u = pivotProfile G r v := hu.2.trans hv.2.symm
  by_cases hrz : G.Adj r z
  · have he := Set.ext_iff.mp huv z
    simpa [pivotProfile,hrz] using he
  · have forward {a : V} (ha : a∈pivotCell G r x) (haz : G.Adj a z) : False := by
      have hzr : z≠r := by intro he; subst z; exact ha.1.2 haz.symm
      have hzN : z∈nonneighbors G r := ⟨hzr,hrz⟩
      exact hz ⟨hzN,(hG.pivotProfile_eq_of_edge ha.1 hzN haz).symm.trans ha.2⟩
    exact iff_of_false (forward hu) (forward hv)

lemma P4Free.pivotCell_distinct_noedge (hG : P4Free G) {r x y u v : V}
    (hu : u∈pivotCell G r x) (hv : v∈pivotCell G r y)
    (hne : pivotProfile G r x ≠ pivotProfile G r y) : ¬G.Adj u v := by
  intro huv
  exact hne (hu.2.symm.trans ((hG.pivotProfile_eq_of_edge hu.1 hv.1 huv).trans hv.2))

lemma pivotCell_eq_of_mem {r x y : V} (hy : y∈pivotCell G r x) :
    pivotCell G r y = pivotCell G r x := by
  ext z
  simp only [pivotCell,Set.mem_setOf_eq,hy.2]

lemma pivotCell_disjoint_or_eq (r x y : V) :
    Disjoint (pivotCell G r x) (pivotCell G r y) ∨ pivotCell G r x = pivotCell G r y := by
  by_cases he : pivotProfile G r x = pivotProfile G r y
  · right; ext z; simp only [pivotCell,Set.mem_setOf_eq,he]
  · left
    apply Set.disjoint_left.mpr
    intro z hx hy
    exact he (hx.2.symm.trans hy.2)

/-- Equality of pivot profiles inside a module is unaffected by vertices outside it. -/
lemma GraphModule.pivotProfile_induce_iff {S : Set V} (hS : GraphModule G S)
    (r x y : S) :
    pivotProfile (G.induce S) r x = pivotProfile (G.induce S) r y ↔
      pivotProfile G r.val x.val = pivotProfile G r.val y.val := by
  constructor
  · intro h
    ext z
    by_cases hz : z∈S
    · exact Set.ext_iff.mp h ⟨z,hz⟩
    · have hx := hS x.val x.property y.val y.property z hz
      change (G.Adj r.val z ∧ G.Adj x.val z) ↔ (G.Adj r.val z ∧ G.Adj y.val z)
      exact and_congr Iff.rfl hx
  · intro h
    ext z
    exact Set.ext_iff.mp h z.val

lemma GraphModule.pivotCell_induce {S : Set V} (hS : GraphModule G S) (r x : S) :
    Subtype.val '' pivotCell (G.induce S) r x = pivotCell G r.val x.val ∩ S := by
  ext y
  constructor
  · rintro ⟨y',⟨hy',hp⟩,rfl⟩
    exact ⟨⟨⟨fun h => hy'.1 (Subtype.ext h),hy'.2⟩,
      (hS.pivotProfile_induce_iff r y' x).mp hp⟩,y'.property⟩
  · rintro ⟨⟨hy,hp⟩,hyS⟩
    refine ⟨⟨y,hyS⟩,⟨⟨?_,hy.2⟩,?_⟩,rfl⟩
    · intro h; exact hy.1 (congrArg Subtype.val h)
    · exact (hS.pivotProfile_induce_iff r ⟨y,hyS⟩ x).mpr hp

/-- Adding only universal outside vertices leaves every nonneighbor profile class
unchanged. This is the graph-semantic core of the cross-sweep recursion. -/
lemma GraphModule.pivotCell_universal_extension {S : Set V} (hS : GraphModule G S)
    (hjoin : ∀ u∈S, ∀ z∉S, G.Adj u z) (r x : S) :
    Subtype.val '' pivotCell (G.induce S) r x = pivotCell G r.val x.val := by
  rw [hS.pivotCell_induce]
  apply Set.inter_eq_left.mpr
  intro y hy
  by_contra hyS
  exact hy.1.2 (hjoin r.val r.property y hyS)

/-- Empty cuts become universal extensions in the complement, so the same
profile-class preservation applies without introducing complement adjacency lists. -/
lemma GraphModule.pivotCell_independent_complement_extension {S : Set V}
    (hS : GraphModule G S) (hunion : ∀ u∈S, ∀ z∉S, ¬G.Adj u z) (r x : S) :
    Subtype.val '' pivotCell (Gᶜ.induce S) r x = pivotCell Gᶜ r.val x.val := by
  apply hS.compl.pivotCell_universal_extension
  intro u hu z hz
  exact (G.compl_adj u z).mpr ⟨fun h => hz (h ▸ hu),hunion u hu z hz⟩

/-- The mathematical first-cell profile after a prefix of pivots. -/
def profileSlice (G : SimpleGraph V) (past : List V) (x : V) : Set V :=
  {y | y∉past ∧ ∀ z∈past, (G.Adj z y ↔ G.Adj z x)}

/-- Once the pivot and all its neighbors have been visited, the first vertex of
an untouched nonneighbor profile class has exactly that class as its slice. -/
theorem P4Free.profileSlice_eq_pivotCell (hG : P4Free G) {r x : V}
    (hx : x∈nonneighbors G r) (past : List V) (hr : r∈past)
    (hneighbors : ∀ z, G.Adj r z → z∈past)
    (hfresh : ∀ y∈pivotCell G r x, y∉past) :
    profileSlice G past x = pivotCell G r x := by
  ext y
  constructor
  · rintro ⟨hy,he⟩
    have hyr : y≠r := fun h => hy (h ▸ hr)
    have hry : ¬G.Adj r y := fun h => hx.2 ((he r hr).mp h)
    refine ⟨⟨hyr,hry⟩,?_⟩
    ext z
    change (G.Adj r z ∧ G.Adj y z) ↔ (G.Adj r z ∧ G.Adj x z)
    by_cases hrz : G.Adj r z
    · have hez := he z (hneighbors z hrz)
      simpa only [G.adj_comm] using (and_congr Iff.rfl hez :
        (G.Adj r z ∧ G.Adj z y) ↔ (G.Adj r z ∧ G.Adj z x))
    · simp only [hrz,false_and]
  · intro hy
    refine ⟨hfresh y hy,?_⟩
    intro z hz
    have hzout : z∉pivotCell G r x := fun hzC => hfresh z hzC hz
    have he := hG.pivotCell_module r x y hy x (mem_pivotCell_self hx) z hzout
    simpa only [G.adj_comm] using he

end HiddenCircuits.DH
