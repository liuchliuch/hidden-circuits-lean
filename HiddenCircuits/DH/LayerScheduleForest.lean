import HiddenCircuits.DH.LayerScheduleSemantics

/-! Disconnected graph-semantic BFS scheduling with one retained original root
per component. All roots, depths, and reachability claims concern ordinary graphs. -/
namespace HiddenCircuits.DH.LayerScheduleForest
open SimpleGraph LayerSchedule
variable {V : Type*} {G : SimpleGraph V}

/-- Literal semantics of the roots and depths computed by the BFS forest. -/
structure Rooting (G : SimpleGraph V) (root : V → V) (depth : V → ℕ) : Prop where
  reachable : ∀v, G.Reachable (root v) v
  constant : ∀u v, G.Reachable u v → root u=root v
  distance : ∀v, depth v=G.dist (root v) v

lemma Rooting.root_fixed {root : V → V} {depth : V → ℕ} (h : Rooting G root depth) (v : V) :
    root (root v)=root v := h.constant _ _ (h.reachable v)

lemma Rooting.depth_root {root : V → V} {depth : V → ℕ} (h : Rooting G root depth) (v : V) :
    depth (root v)=0 := by rw [h.distance,h.root_fixed,dist_self]

lemma Rooting.same_root_iff {root : V → V} {depth : V → ℕ} (h : Rooting G root depth) (u v : V) :
    root u=root v ↔ G.Reachable u v := by
  constructor
  · intro he; exact (h.reachable u).symm.trans (he ▸ h.reachable v)
  · exact h.constant u v

/-- The actual live mask retains roots and both original reachability relations. -/
structure LiveInvariant (G : SimpleGraph V) (root : V → V) (depth : V → ℕ) (alive : Set V) : Prop where
  roots_alive : ∀v, root v∈alive
  reachable : ∀a b:alive, (G.induce alive).Reachable a b ↔ G.Reachable a.val b.val
  sameDepth : ∀a b:alive,
    ((sameDepthGraph G depth).induce alive).Reachable a b ↔ (sameDepthGraph G depth).Reachable a.val b.val

lemma LiveInvariant.initial (root : V → V) (depth : V → ℕ) : LiveInvariant G root depth Set.univ := by
  refine ⟨by simp,?_,?_⟩
  · intro a b
    constructor
    · intro h; exact h.map (Embedding.induce Set.univ).toHom
    · intro h
      let f : G →g G.induce Set.univ := ⟨fun v => ⟨v,Set.mem_univ _⟩,fun h => h⟩
      exact h.map f
  · intro a b
    constructor
    · intro h; exact h.map (Embedding.induce Set.univ).toHom
    · intro h
      let f : sameDepthGraph G depth →g (sameDepthGraph G depth).induce Set.univ :=
        ⟨fun v => ⟨v,Set.mem_univ _⟩,fun h => h⟩
      exact h.map f

/-- Natural graph distance remains the original component-root depth despite
disconnected original/live graphs; reachability is supplied by the proved mask invariant. -/
lemma live_depth (hG : DistanceHereditaryGraph G) {root : V → V} {depth : V → ℕ}
    (hroot : Rooting G root depth) {alive : Set V} (hi : LiveInvariant G root depth alive) (v : alive) :
    (G.induce alive).dist ⟨root v.val,hi.roots_alive v.val⟩ v=depth v.val := by
  have hr := (hi.reachable ⟨root v.val,hi.roots_alive v.val⟩ v).mpr (hroot.reachable v.val)
  exact (hG.induce_dist_of_reachable hr).trans (hroot.distance v.val).symm

/-- Original predecessor rows in a rooted forest can use only depth equality
and graph adjacency; the component root is forced by each edge. -/
def forestPredecessors (G : SimpleGraph V) (depth : V → ℕ) (u : V) : Set V :=
  {v | G.Adj v u ∧ depth v+1=depth u}

lemma forestPredecessors_eq {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth) (u : V) :
    forestPredecessors G depth u=predecessors G (root u) u := by
  ext v
  change (G.Adj v u ∧ depth v+1=depth u) ↔ (G.Adj v u ∧ G.dist (root u) v+1=G.dist (root u) u)
  apply and_congr_right
  intro hv
  have he := hroot.constant v u hv.reachable
  rw [hroot.distance v,hroot.distance u,he]

lemma live_forest_predecessor_iff (hG : DistanceHereditaryGraph G)
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u v : alive) :
    v∈predecessors (G.induce alive) ⟨root u.val,hi.roots_alive u.val⟩ u ↔
      v.val∈forestPredecessors G depth u.val := by
  change (G.Adj v.val u.val ∧ _ = _) ↔ (G.Adj v.val u.val ∧ _ = _)
  apply and_congr_right
  intro hv
  have he := hroot.constant v.val u.val hv.reachable
  have hdv := live_depth hG hroot hi v
  have hdu := live_depth hG hroot hi u
  have hroots : (⟨root v.val,hi.roots_alive v.val⟩ : alive)=⟨root u.val,hi.roots_alive u.val⟩ := Subtype.ext he
  rw [hroots] at hdv
  rw [hdv,hdu]

lemma live_forest_predecessors_image (hG : DistanceHereditaryGraph G)
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u : alive) :
    Subtype.val '' predecessors (G.induce alive) ⟨root u.val,hi.roots_alive u.val⟩ u =
      forestPredecessors G depth u.val ∩ alive := by
  ext v
  constructor
  · rintro ⟨v',hv,rfl⟩; exact ⟨(live_forest_predecessor_iff hG hroot hi u v').mp hv,v'.property⟩
  · rintro ⟨hv,ha⟩
    exact ⟨⟨v,ha⟩,(live_forest_predecessor_iff hG hroot hi u ⟨v,ha⟩).mpr hv,rfl⟩

/-- Pendants preserve every component, not merely whole-graph connectivity. -/
lemma pendant_reachable_delete {keep v : V} (hp : PendantPair G keep v)
    (a b : {x : V | x≠v}) : (G.induce {x | x≠v}).Reachable a b ↔ G.Reachable a.val b.val := by
  classical
  constructor
  · intro h; exact h.map (Embedding.induce {x | x≠v}).toHom
  · intro h
    let f := mergeRep keep v hp.distinct
    have hf : ∀x y, G.Adj x y → (G.induce {x | x≠v}).Reachable (f x) (f y) := by
      intro x y hxy
      by_cases he : f x=f y
      · rw [he]
      · have ha : (G.induce {x | x≠v}).Adj (f x) (f y) := ((hp.adj_merge x y he).mp hxy).2.2
        exact ha.reachable
    have hr := reachable_map_weak f hf h
    simpa only [f,mergeRep_surviving keep v a.val hp.distinct a.property,
      mergeRep_surviving keep v b.val hp.distinct b.property] using hr

/-- A connected-component support is always a module of the whole graph. -/
lemma component_module (C : G.ConnectedComponent) : GraphModule G C.supp := by
  intro u hu v hv x hx
  exact iff_of_false (fun h => hx (C.mem_supp_of_adj_mem_supp hu h))
    (fun h => hx (C.mem_supp_of_adj_mem_supp hv h))

/-- The retained vertices with a fixed original root are exactly one live component. -/
lemma root_component_support {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u : alive) :
    {v:alive | root v.val=root u.val}=((G.induce alive).connectedComponentMk u).supp := by
  ext v
  change root v.val=root u.val ↔ (G.induce alive).connectedComponentMk v=(G.induce alive).connectedComponentMk u
  rw [ConnectedComponent.eq,hi.reachable]
  exact hroot.same_root_iff _ _

lemma root_component_connected {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u : alive) :
    ((G.induce alive).induce {v:alive | root v.val=root u.val}).Connected := by
  rw [root_component_support hroot hi u]
  exact ((G.induce alive).connectedComponentMk u).connected_toSimpleGraph

lemma root_component_module {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u : alive) :
    GraphModule (G.induce alive) {v:alive | root v.val=root u.val} := by
  rw [root_component_support hroot hi u]
  exact component_module _

lemma component_predecessors_image (hG : DistanceHereditaryGraph G)
    (C : G.ConnectedComponent) (r u : C.supp) :
    Subtype.val '' predecessors (G.induce C.supp) r u=predecessors G r.val u.val := by
  rw [LayerSchedule.live_predecessors_image hG C.supp C.connected_toSimpleGraph]
  apply Set.inter_eq_left.mpr
  intro v hv
  exact C.mem_supp_of_adj_mem_supp u.property hv.1.symm

lemma component_predecessors_subset_iff (hG : DistanceHereditaryGraph G)
    (C : G.ConnectedComponent) (r u v : C.supp) :
    predecessors (G.induce C.supp) r u ⊆ predecessors (G.induce C.supp) r v ↔
      predecessors G r.val u.val ⊆ predecessors G r.val v.val := by
  constructor
  · intro h x hx
    have hxC := C.mem_supp_of_adj_mem_supp u.property hx.1.symm
    exact (LayerSchedule.live_predecessor_iff hG C.supp C.connected_toSimpleGraph r v ⟨x,hxC⟩).mp
      (h ((LayerSchedule.live_predecessor_iff hG C.supp C.connected_toSimpleGraph r u ⟨x,hxC⟩).mpr hx))
  · intro h x hx
    exact (LayerSchedule.live_predecessor_iff hG C.supp C.connected_toSimpleGraph r v x).mpr
      (h ((LayerSchedule.live_predecessor_iff hG C.supp C.connected_toSimpleGraph r u x).mp hx))

/-- The connected BFS laminarity theorem applies inside one original component
and transports back to the whole disconnected graph exactly. -/
theorem predecessors_laminar_reachable (hG : DistanceHereditaryGraph G) {r u v : V}
    (hu : G.Reachable r u) (hv : G.Reachable r v) (hlevel : G.dist r u=G.dist r v) :
    Disjoint (predecessors G r u) (predecessors G r v) ∨
      predecessors G r u ⊆ predecessors G r v ∨ predecessors G r v ⊆ predecessors G r u := by
  let C := G.connectedComponentMk r
  let r' : C.supp := ⟨r,rfl⟩
  let u' : C.supp := ⟨u,ConnectedComponent.sound hu.symm⟩
  let v' : C.supp := ⟨v,ConnectedComponent.sound hv.symm⟩
  have hd : (G.induce C.supp).dist r' u'=(G.induce C.supp).dist r' v' := by
    rw [hG C.supp C.connected_toSimpleGraph,hG C.supp C.connected_toSimpleGraph]
    exact hlevel
  rcases (hG.induce C.supp).predecessors_laminar C.connected_toSimpleGraph r' u' v' hd with h | h | h
  · left
    rw [←component_predecessors_image hG C r' u',←component_predecessors_image hG C r' v']
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,he⟩ ⟨b,hb,hbval⟩
    have hab : a=b := Subtype.ext (he.trans hbval.symm)
    exact Set.disjoint_left.mp h ha (hab ▸ hb)
  · exact Or.inr (Or.inl ((component_predecessors_subset_iff hG C r' u' v').mp h))
  · exact Or.inr (Or.inr ((component_predecessors_subset_iff hG C r' v' u').mp h))

/-- Component-local predecessor minimality gives a whole-graph module; there are
no edges to vertices outside the component. -/
theorem minimal_predecessors_module_reachable (hG : DistanceHereditaryGraph G) {r u : V}
    (hu : G.Reachable r u)
    (hmin : ∀z, G.Reachable r z → G.dist r z=G.dist r u →
      predecessors G r z ⊆ predecessors G r u → predecessors G r u ⊆ predecessors G r z) :
    GraphModule G (predecessors G r u) := by
  let C := G.connectedComponentMk r
  let r' : C.supp := ⟨r,rfl⟩
  let u' : C.supp := ⟨u,ConnectedComponent.sound hu.symm⟩
  have hm : GraphModule (G.induce C.supp) (predecessors (G.induce C.supp) r' u') := by
    apply (hG.induce C.supp).minimal_predecessors_module C.connected_toSimpleGraph r' u'
    intro z hz hsub
    have hzReach : G.Reachable r z.val := C.reachable_of_mem_supp r'.property z.property
    have hzDist : G.dist r z.val=G.dist r u := by
      simpa only [hG C.supp C.connected_toSimpleGraph] using hz
    exact (component_predecessors_subset_iff hG C r' u' z).mpr
      (hmin z.val hzReach hzDist ((component_predecessors_subset_iff hG C r' z u').mp hsub))
  have hLift := (component_module C).induce_lift hm
  rwa [component_predecessors_image hG C r' u'] at hLift

/-- A component-local farthest connected layer block is a cograph module of the
entire disconnected graph, by exact induced-subgraph lifting. -/
theorem farthest_component_module (hG : DistanceHereditaryGraph G)
    (C : G.ConnectedComponent) (r : C.supp) (k : ℕ) (S : Set V)
    (hSC : S⊆C.supp) (hmax : ∀v:C.supp, G.dist r.val v.val≤k)
    (hlevel : ∀v∈S, G.dist r.val v=k) (hconn : (G.induce S).Preconnected)
    (hclosed : ∀u∈S, ∀v, G.Adj u v → G.dist r.val v=k → v∈S) :
    GraphModule G S ∧ P4Free (G.induce S) := by
  let T : Set C.supp := {v | v.val∈S}
  have himage : Subtype.val '' T=S := by
    ext v
    constructor
    · rintro ⟨v',hv,rfl⟩; exact hv
    · intro hv; exact ⟨⟨v,hSC hv⟩,hv,rfl⟩
  have hconn' : ((G.induce C.supp).induce T).Preconnected := by
    let f : G.induce S →g (G.induce C.supp).induce T := {
      toFun x := ⟨⟨x.val,hSC x.property⟩,x.property⟩
      map_rel' := by intro u v h; exact h }
    intro a b
    exact (hconn ⟨a.val.val,a.property⟩ ⟨b.val.val,b.property⟩).map f
  have hmodule : GraphModule (G.induce C.supp) T := by
    apply (hG.induce C.supp).farthest_layer_module C.connected_toSimpleGraph r k
    · intro v; rw [hG C.supp C.connected_toSimpleGraph]; exact hmax v
    · intro v hv; rw [hG C.supp C.connected_toSimpleGraph]; exact hlevel v.val hv
    · exact hconn'
    · intro u hu v huv hv
      apply hclosed u.val hu v.val huv
      simpa only [hG C.supp C.connected_toSimpleGraph] using hv
  have hm := (component_module C).induce_lift hmodule
  rw [himage] at hm
  refine ⟨hm,?_⟩
  let f : G.induce S ↪g (G.induce C.supp).induce {v | (G.induce C.supp).dist r v=k} := {
    toFun x := ⟨⟨x.val,hSC x.property⟩,by
      change (G.induce C.supp).dist r ⟨x.val,hSC x.property⟩=k
      rw [hG C.supp C.connected_toSimpleGraph]
      exact hlevel x.val x.property⟩
    inj' := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : {v:C.supp | (G.induce C.supp).dist r v=k} => z.val.val) he)
    map_rel_iff' := by intro x y; rfl }
  exact ((hG.induce C.supp).layer_p4Free C.connected_toSimpleGraph r k).of_embedding f

lemma root_eq_of_live_reachable {root : V → V} {depth : V → ℕ}
    (hroot : Rooting G root depth) {alive : Set V} (hi : LiveInvariant G root depth alive)
    (u v : alive) (hr : (G.induce alive).Reachable ⟨root u.val,hi.roots_alive u.val⟩ v) :
    root v.val=root u.val := by
  have he := hroot.constant (root u.val) v.val ((hi.reachable _ _).mp hr)
  rw [hroot.root_fixed] at he
  exact he.symm

lemma live_depth_of_same_root (hG : DistanceHereditaryGraph G)
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u v : alive)
    (he : root v.val=root u.val) :
    (G.induce alive).dist ⟨root u.val,hi.roots_alive u.val⟩ v=depth v.val := by
  have hd := live_depth hG hroot hi v
  have hr : (⟨root v.val,hi.roots_alive v.val⟩ : alive)=⟨root u.val,hi.roots_alive u.val⟩ := Subtype.ext he
  rwa [hr] at hd

/-- Phase A for the disconnected original graph: a surviving original
same-depth component at the current maximum depth is a cograph module of the
whole current graph, not just its original connected component. -/
theorem phaseA_module (hG : DistanceHereditaryGraph G)
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (k : ℕ)
    (hmax : ∀v:alive, depth v.val≤k)
    (C : (sameDepthGraph G depth).ConnectedComponent)
    (u : alive) (hu : u.val∈C.supp) (huk : depth u.val=k) :
    GraphModule (G.induce alive) {v:alive | v.val∈C.supp} ∧
      P4Free ((G.induce alive).induce {v:alive | v.val∈C.supp}) := by
  let H := G.induce alive
  let ru : alive := ⟨root u.val,hi.roots_alive u.val⟩
  let D := H.connectedComponentMk ru
  let S : Set alive := {v | v.val∈C.supp}
  have hDdepth (v : D.supp) : H.dist ru v.val=depth v.val.val := by
    have hr : H.Reachable ru v.val := D.reachable_of_mem_supp (show ru∈D.supp from rfl) v.property
    exact live_depth_of_same_root hG hroot hi u v.val (root_eq_of_live_reachable hroot hi u v.val hr)
  have hSC : S⊆D.supp := by
    intro v hv
    have hruv := C.reachable_of_mem_supp hu hv
    let forget : sameDepthGraph G depth →g G := ⟨id,fun h => h.1⟩
    have horig : G.Reachable (root u.val) v.val := (hroot.reachable u.val).trans (hruv.map forget)
    have hcur := (hi.reachable ru v).mpr horig
    exact ConnectedComponent.sound hcur.symm
  have hdepth : ∀v∈S, depth v.val=k := by
    intro v hv
    exact (sameDepthGraph_reachable_depth depth (C.reachable_of_mem_supp hu hv)).symm.trans huk
  have hcK := LayerSchedule.component_restrict_connected (sameDepthGraph G depth) alive hi.sameDepth C u hu
  let forget : (((sameDepthGraph G depth).induce alive).induce S) →g H.induce S :=
    ⟨id,fun h => h.1⟩
  have hconn : (H.induce S).Preconnected := by
    intro a b
    exact (hcK.preconnected a b).map forget
  apply farthest_component_module (hG.induce alive) D ⟨ru,rfl⟩ k S hSC
  · intro v; rw [hDdepth]; exact hmax v.val
  · intro v hv
    exact (hDdepth ⟨v,hSC hv⟩).trans (hdepth v hv)
  · exact hconn
  · intro v hv w hvw hw
    have hrw : H.Reachable ru w :=
      (D.reachable_of_mem_supp (show ru∈D.supp from rfl) (hSC hv)).trans hvw.reachable
    have hdw := live_depth_of_same_root hG hroot hi u w (root_eq_of_live_reachable hroot hi u w hrw)
    have hwk : depth w.val=k := hdw.symm.trans hw
    exact C.mem_supp_of_adj_mem_supp hv ⟨hvw,(hdepth v hv).trans hwk.symm⟩

lemma forest_predecessors_laminar (hG : DistanceHereditaryGraph G)
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth) (u v : V)
    (hr : root u=root v) (hd : depth u=depth v) :
    Disjoint (forestPredecessors G depth u) (forestPredecessors G depth v) ∨
      forestPredecessors G depth u ⊆ forestPredecessors G depth v ∨
      forestPredecessors G depth v ⊆ forestPredecessors G depth u := by
  rw [forestPredecessors_eq hroot u,forestPredecessors_eq hroot v,←hr]
  apply predecessors_laminar_reachable hG (hroot.reachable u)
  · simpa only [hr] using hroot.reachable v
  · simpa only [hroot.distance,←hr] using hd

lemma live_forest_predecessor_iff_same_root (hG : DistanceHereditaryGraph G)
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u z v : alive)
    (he : root z.val=root u.val) :
    v∈predecessors (G.induce alive) ⟨root u.val,hi.roots_alive u.val⟩ z ↔
      v.val∈forestPredecessors G depth z.val := by
  have hroots : (⟨root z.val,hi.roots_alive z.val⟩ : alive)=⟨root u.val,hi.roots_alive u.val⟩ := Subtype.ext he
  rw [←hroots]
  exact live_forest_predecessor_iff hG hroot hi z v

/-- Phase B uses only the static original predecessor sizes within the selected
original component and level; arbitrary prior common restrictions are allowed. -/
theorem phaseB_module [Finite V] (hG : DistanceHereditaryGraph G)
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {alive : Set V} (hi : LiveInvariant G root depth alive) (u : alive)
    (hpos : 0<depth u.val)
    (hsize : ∀z:alive, root z.val=root u.val → depth z.val=depth u.val →
      (forestPredecessors G depth u.val).ncard≤(forestPredecessors G depth z.val).ncard) :
    GraphModule (G.induce alive)
      (predecessors (G.induce alive) ⟨root u.val,hi.roots_alive u.val⟩ u) ∧
      P4Free ((G.induce alive).induce
        (predecessors (G.induce alive) ⟨root u.val,hi.roots_alive u.val⟩ u)) := by
  let H := G.induce alive
  let ru : alive := ⟨root u.val,hi.roots_alive u.val⟩
  have hDH := hG.induce alive
  have hru : H.Reachable ru u := (hi.reachable ru u).mpr (hroot.reachable u.val)
  refine ⟨minimal_predecessors_module_reachable hDH hru ?_,hDH.predecessors_p4Free ru u⟩
  intro z hrz hzd hsub
  have hroots := root_eq_of_live_reachable hroot hi u z hrz
  have hzu : depth z.val=depth u.val := by
    rw [live_depth_of_same_root hG hroot hi u z hroots,live_depth hG hroot hi u] at hzd
    exact hzd
  rcases forest_predecessors_laminar hG hroot u.val z.val hroots.symm hzu.symm with hd | hinc | hinc
  · have hzpos : 0<H.dist ru z := by rw [hzd,live_depth hG hroot hi u]; exact hpos
    obtain ⟨x,hx⟩ := predecessors_nonempty hrz hzpos
    exact False.elim (Set.disjoint_left.mp hd
      ((live_forest_predecessor_iff hG hroot hi u x).mp (hsub hx))
      ((live_forest_predecessor_iff_same_root hG hroot hi u z x hroots).mp hx))
  · intro x hx
    exact (live_forest_predecessor_iff_same_root hG hroot hi u z x hroots).mpr
      (hinc ((live_forest_predecessor_iff hG hroot hi u x).mp hx))
  · have he := Set.eq_of_subset_of_ncard_le hinc (hsize z hroots hzu)
    intro x hx
    exact (live_forest_predecessor_iff_same_root hG hroot hi u z x hroots).mpr
      (he.symm ▸ ((live_forest_predecessor_iff hG hroot hi u x).mp hx))

/-- The original roots/depths remain a valid rooted BFS forest of the literal
live graph. No connectedness of the whole graph is required. -/
def liveRoot {root : V → V} {depth : V → ℕ} {alive : Set V}
    (hi : LiveInvariant G root depth alive) (v : alive) : alive :=
  ⟨root v.val,hi.roots_alive v.val⟩

lemma liveRooting (hG : DistanceHereditaryGraph G) {root : V → V} {depth : V → ℕ}
    (hroot : Rooting G root depth) {alive : Set V} (hi : LiveInvariant G root depth alive) :
    Rooting (G.induce alive) (liveRoot hi) (fun v => depth v.val) := by
  refine ⟨?_,?_,?_⟩
  · intro v; exact (hi.reachable (liveRoot hi v) v).mpr (hroot.reachable v.val)
  · intro u v huv
    exact Subtype.ext (hroot.constant u.val v.val ((hi.reachable u v).mp huv))
  · intro v; exact (live_depth hG hroot hi v).symm

lemma predecessor_module_survivors_reachable [DecidableEq V]
    {r u keep : V} {S : Finset V} (hr : G.Reachable r u)
    (hS : (S : Set V)=predecessors G r u) (hk : keep∈S) :
    (r=keep ∨ r∉S) ∧ u∉S := by
  constructor
  · by_cases hrs : r∈S
    · left
      have hrp : r∈predecessors G r u := hS ▸ hrs
      have hkp : keep∈predecessors G r u := hS ▸ hk
      have hreach : G.Reachable r keep := hr.trans hkp.1.symm.reachable
      have hrd := hrp.2
      have hkd := hkp.2
      simp only [dist_self] at hrd
      exact hreach.dist_eq_zero_iff.mp (by omega)
    · exact Or.inr hrs
  · intro hu
    have hup : u∈predecessors G r u := hS ▸ hu
    exact hup.1.ne rfl

/-- A positive-depth one-layer module contains no original component root. -/
lemma roots_survive_positive_module {root : V → V} {depth : V → ℕ}
    (hroot : Rooting G root depth) {S : Set V} {k : ℕ} (hk : 0<k)
    (hS : ∀v∈S, depth v=k) : ∀v, root v∉S := by
  intro v hv
  have he := hS (root v) hv
  rw [hroot.depth_root] at he
  omega

/-- Even the depth-one predecessor collapse retains its component root: its
predecessor block is then the singleton root. Roots of other components lie outside. -/
lemma roots_survive_predecessor_module [DecidableEq V]
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {u keep : V} {S : Finset V} (hS : (S : Set V)=forestPredecessors G depth u) (hk : keep∈S) :
    ∀v, root v=keep ∨ root v∉S := by
  have hS' : (S : Set V)=predecessors G (root u) u := hS.trans (forestPredecessors_eq hroot u)
  have hs := (predecessor_module_survivors_reachable (hroot.reachable u) hS' hk).1
  intro v
  by_cases hv : root v∈S
  · have hp : root v∈forestPredecessors G depth u := hS ▸ hv
    have he := hroot.constant (root v) u hp.1.reachable
    rw [hroot.root_fixed] at he
    have hru : root u∈S := he ▸ hv
    exact Or.inl (he.trans (hs.resolve_right (not_not.mpr hru)))
  · exact Or.inr hv

lemma roots_survive_positive_pendant {root : V → V} {depth : V → ℕ}
    (hroot : Rooting G root depth) {v : V} (hv : 0<depth v) : ∀u, root u≠v := by
  intro u he
  have hd := hroot.depth_root u
  rw [he] at hd
  omega

/-- Predecessor contraction leaves an actual pendant in a disconnected graph.
Only the selected root's reachable component needs the farthest-layer bound. -/
theorem pendant_after_predecessors_reachable [DecidableEq V]
    {r u keep : V} {S : Finset V} (hr : G.Reachable r u)
    (hS : (S : Set V)=predecessors G r u) (hk : keep∈S)
    (u' : ModuleSurvivor S keep) (hu : u'.val=u)
    (hmax : ∀v, G.Reachable r v → G.dist r v≤G.dist r u)
    (hind : ∀v, G.dist r v=G.dist r u → ¬G.Adj u v) :
    PendantPair (G.induce {x | x=keep ∨ x∉S}) (moduleKeep S keep) u' := by
  have hkeep : keep∈predecessors G r u := hS ▸ hk
  refine ⟨?_,?_⟩
  · change G.Adj u'.val keep
    rw [hu]
    exact hkeep.1.symm
  · intro v huv
    have hEdge : G.Adj u v.val := by
      change G.Adj u'.val v.val at huv
      simpa only [hu] using huv
    have hReach := hr.trans hEdge.reachable
    have hd := hEdge.diff_dist_adj (u := r)
    have hm := hmax v.val hReach
    have hne : G.dist r v.val≠G.dist r u := fun he => hind v.val he hEdge
    have hp : v.val∈predecessors G r u := ⟨hEdge.symm,by omega⟩
    have hvS : v.val∈S := by
      change v.val∈(S : Set V)
      rw [hS]
      exact hp
    exact Subtype.ext (v.property.resolve_right (not_not.mpr hvS))

/-- The depth-array form directly consumed after phase B's predecessor collapse. -/
theorem forest_pendant_after_predecessors [DecidableEq V]
    {root : V → V} {depth : V → ℕ} (hroot : Rooting G root depth)
    {u keep : V} {S : Finset V} (hS : (S : Set V)=forestPredecessors G depth u) (hk : keep∈S)
    (u' : ModuleSurvivor S keep) (hu : u'.val=u)
    (hmax : ∀v, root v=root u → depth v≤depth u)
    (hind : ∀v, depth v=depth u → ¬G.Adj u v) :
    PendantPair (G.induce {x | x=keep ∨ x∉S}) (moduleKeep S keep) u' := by
  apply pendant_after_predecessors_reachable (hroot.reachable u)
    (hS.trans (forestPredecessors_eq hroot u)) hk u' hu
  · intro v hv
    have hrv := hroot.constant (root u) v hv
    rw [hroot.root_fixed] at hrv
    have hd := hmax v hrv.symm
    simpa only [hroot.distance,hrv] using hd
  · intro v hv he
    have hrv := hroot.constant u v he.reachable
    have hd : depth v=depth u := by simpa only [hroot.distance,←hrv] using hv
    exact hind v hd he

end HiddenCircuits.DH.LayerScheduleForest
