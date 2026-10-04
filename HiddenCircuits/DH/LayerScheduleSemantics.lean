import HiddenCircuits.DH.LayerSchedule

/-! Graph-semantic invariants for the static original BFS schedule. Live graphs
are literal induced graphs, and every deletion step is an actual module or
pendant operation; no pruning or scheduling certificate defines the graph class. -/
namespace HiddenCircuits.DH.LayerSchedule
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Delete cross-depth edges while retaining the original vertex labels. -/
def sameDepthGraph (G : SimpleGraph V) (depth : V → ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ depth u=depth v
  symm := by intro u v h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := ⟨by intro u h; exact h.1.ne rfl⟩

@[simp] lemma sameDepthGraph_adj (depth : V → ℕ) (u v : V) :
    (sameDepthGraph G depth).Adj u v ↔ G.Adj u v ∧ depth u=depth v := Iff.rfl

lemma sameDepthGraph_induce (depth : V → ℕ) (alive : Set V) :
    sameDepthGraph (G.induce alive) (fun v => depth v.val) = (sameDepthGraph G depth).induce alive := by
  ext u v; rfl

lemma sameDepthGraph_reachable_depth (depth : V → ℕ) {u v : V}
    (h : (sameDepthGraph G depth).Reachable u v) : depth u=depth v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons he p ih => exact he.2.trans ih

/-- A genuine one-depth module stays a module when cross-depth edges are removed. -/
lemma GraphModule.sameDepth {S : Set V} (hm : HiddenCircuits.DH.GraphModule G S)
    (depth : V → ℕ) (k : ℕ) (hdepth : ∀v∈S, depth v=k) :
    HiddenCircuits.DH.GraphModule (sameDepthGraph G depth) S := by
  intro u hu v hv x hx
  change (G.Adj u x ∧ depth u=depth x) ↔ (G.Adj v x ∧ depth v=depth x)
  have he : depth u=depth v := (hdepth u hu).trans (hdepth v hv).symm
  rw [he]
  exact and_congr (hm u hu v hv x hx) Iff.rfl

/-- Static same-depth component classes are preserved by every actual one-depth
module contraction, including modules spanning several components. -/
theorem module_sameDepth_reachable [DecidableEq V] {S : Finset V} {keep : V}
    (hm : HiddenCircuits.DH.GraphModule G (S : Set V)) (hk : keep∈S)
    (depth : V → ℕ) (k : ℕ) (hdepth : ∀v∈S, depth v=k)
    (a b : ModuleSurvivor S keep) :
    (sameDepthGraph (G.induce {v | v=keep ∨ v∉S}) (fun v => depth v.val)).Reachable a b ↔
      (sameDepthGraph G depth).Reachable a.val b.val := by
  rw [sameDepthGraph_induce]
  exact (GraphModule.sameDepth hm depth k hdepth).reachable_moduleDelete hk a b

/-- Deleting an isolated vertex preserves reachability between all other vertices. -/
lemma reachable_delete_isolated {v : V} (hv : ∀x, ¬G.Adj v x)
    (a b : {x : V | x≠v}) :
    (G.induce {x | x≠v}).Reachable a b ↔ G.Reachable a.val b.val := by
  classical
  constructor
  · intro h; exact h.map (Embedding.induce {x | x≠v}).toHom
  · intro h
    let f : V → {x : V | x≠v} := fun x => if hx : x=v then a else ⟨x,hx⟩
    have hf (x : V) (hx : x≠v) : f x=⟨x,hx⟩ := by simp [f,hx]
    have hedge : ∀x y, G.Adj x y → (G.induce {x | x≠v}).Reachable (f x) (f y) := by
      intro x y hxy
      have hx : x≠v := fun he => hv y (he ▸ hxy)
      have hy : y≠v := fun he => hv x (he ▸ hxy.symm)
      rw [hf x hx,hf y hy]
      exact (show (G.induce {x | x≠v}).Adj ⟨x,hx⟩ ⟨y,hy⟩ from hxy).reachable
    have hr := reachable_map_weak f hedge h
    simpa only [hf a.val a.property,hf b.val b.property] using hr

/-- A pendant edge joins distinct depths, so removing its leaf changes no
same-depth connected component on the remaining vertices. -/
theorem pendant_sameDepth_reachable {keep v : V} (hp : PendantPair G keep v)
    (depth : V → ℕ) (hne : depth v≠depth keep) (a b : {x : V | x≠v}) :
    (sameDepthGraph (G.induce {x | x≠v}) (fun x => depth x.val)).Reachable a b ↔
      (sameDepthGraph G depth).Reachable a.val b.val := by
  rw [sameDepthGraph_induce]
  apply reachable_delete_isolated
  intro x hx
  have he := hp.unique x hx.1
  exact hne (he ▸ hx.2)

/-- Connected literal live induced graphs retain all original BFS distances. -/
lemma live_dist (hG : DistanceHereditaryGraph G) (alive : Set V)
    (hc : (G.induce alive).Connected) (r v : alive) :
    (G.induce alive).dist r v=G.dist r.val v.val := hG alive hc r v

lemma live_predecessor_iff (hG : DistanceHereditaryGraph G) (alive : Set V)
    (hc : (G.induce alive).Connected) (r u v : alive) :
    v∈predecessors (G.induce alive) r u ↔ v.val∈predecessors G r.val u.val := by
  change (G.Adj v.val u.val ∧ (G.induce alive).dist r v+1=(G.induce alive).dist r u) ↔ _
  rw [live_dist hG alive hc,live_dist hG alive hc]
  rfl

/-- Current predecessor rows are exactly the original rows filtered by alive. -/
lemma live_predecessors_image (hG : DistanceHereditaryGraph G) (alive : Set V)
    (hc : (G.induce alive).Connected) (r u : alive) :
    Subtype.val '' predecessors (G.induce alive) r u = predecessors G r.val u.val ∩ alive := by
  ext v
  constructor
  · rintro ⟨v',hv,rfl⟩
    exact ⟨(live_predecessor_iff hG alive hc r u v').mp hv,v'.property⟩
  · rintro ⟨hv,ha⟩
    exact ⟨⟨v,ha⟩,(live_predecessor_iff hG alive hc r u ⟨v,ha⟩).mpr hv,rfl⟩

/-- Every actual module deletion preserves the prior root distances, provided
that the root is retained. Repeating this equality keeps the original depths. -/
lemma moduleDelete_dist [DecidableEq V] (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    {S : Finset V} {keep : V} (hm : HiddenCircuits.DH.GraphModule G (S : Set V)) (hk : keep∈S)
    (r v : ModuleSurvivor S keep) :
    (G.induce {x | x=keep ∨ x∉S}).dist r v=G.dist r.val v.val :=
  hG _ (hm.connected_moduleDelete hk hc) r v

lemma pendantDelete_dist (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    {keep v : V} (hp : PendantPair G keep v) (r x : {a : V | a≠v}) :
    (G.induce {a | a≠v}).dist r x=G.dist r.val x.val := hG _ (hp.connected_delete hc) r x

/-- A surviving original component has exactly one current component, as a
literal equality of supports. Empty original components disappear completely. -/
lemma component_restrict_support (K : SimpleGraph V) (alive : Set V)
    (hreach : ∀a b:alive, (K.induce alive).Reachable a b ↔ K.Reachable a.val b.val)
    (C : K.ConnectedComponent) (a : alive) (ha : a.val∈C.supp) :
    {x:alive | x.val∈C.supp} = ((K.induce alive).connectedComponentMk a).supp := by
  ext x
  have hC : K.connectedComponentMk a.val=C := ha
  rw [←hC]
  change K.connectedComponentMk x.val=K.connectedComponentMk a.val ↔
    (K.induce alive).connectedComponentMk x=(K.induce alive).connectedComponentMk a
  rw [ConnectedComponent.eq,ConnectedComponent.eq]
  exact (hreach x a).symm

lemma component_restrict_connected (K : SimpleGraph V) (alive : Set V)
    (hreach : ∀a b:alive, (K.induce alive).Reachable a b ↔ K.Reachable a.val b.val)
    (C : K.ConnectedComponent) (a : alive) (ha : a.val∈C.supp) :
    ((K.induce alive).induce {x:alive | x.val∈C.supp}).Connected := by
  rw [component_restrict_support K alive hreach C a ha]
  exact ((K.induce alive).connectedComponentMk a).connected_toSimpleGraph

/-- All vertices of an original same-depth component have exactly the same
original predecessor set, so choosing a different survivor changes no size key. -/
lemma sameDepth_predecessors_eq (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    (r : V) {u v : V} (h : (sameDepthGraph G (G.dist r)).Reachable u v) :
    predecessors G r u=predecessors G r v := by
  have hedge {a b : V} (hab : (sameDepthGraph G (G.dist r)).Adj a b) :
      predecessors G r a=predecessors G r b := by
    ext x
    constructor
    · intro hx
      exact ⟨hG.adjacent_same_level_predecessors (hc r x) hab.1 hx.2 hab.2 hx.1,hx.2.trans hab.2⟩
    · intro hx
      exact ⟨hG.adjacent_same_level_predecessors (hc r x) hab.1.symm hx.2 hab.2.symm hx.1,hx.2.trans hab.2.symm⟩
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons he p ih => exact (hedge he).trans ih

/-- A nonempty live restriction of an original farthest same-depth component is
an actual current-graph cograph module. The reachability invariant is preserved
by the module/pendant lemmas above, including disappearance of whole components. -/
theorem farthest_static_component (hG : DistanceHereditaryGraph G)
    (alive : Set V) (hc : (G.induce alive).Connected) (r : alive) (k : ℕ)
    (hmax : ∀v:alive, G.dist r.val v.val≤k)
    (hreach : ∀a b:alive,
      ((sameDepthGraph G (G.dist r.val)).induce alive).Reachable a b ↔
        (sameDepthGraph G (G.dist r.val)).Reachable a.val b.val)
    (C : (sameDepthGraph G (G.dist r.val)).ConnectedComponent)
    (a : alive) (ha : a.val∈C.supp) (hlevel : G.dist r.val a.val=k) :
    HiddenCircuits.DH.GraphModule (G.induce alive) {v:alive | v.val∈C.supp} ∧
      P4Free ((G.induce alive).induce {v:alive | v.val∈C.supp}) := by
  let S : Set alive := {v | v.val∈C.supp}
  have hdepth : ∀v∈S, G.dist r.val v.val=k := by
    intro v hv
    have he := sameDepthGraph_reachable_depth (G.dist r.val) (C.reachable_of_mem_supp ha hv)
    exact he.symm.trans hlevel
  have hcurrent : ∀v∈S, (G.induce alive).dist r v=k := by
    intro v hv
    rw [live_dist hG alive hc]
    exact hdepth v hv
  have hconnK := component_restrict_connected (sameDepthGraph G (G.dist r.val)) alive hreach C a ha
  let forget : (((sameDepthGraph G (G.dist r.val)).induce alive).induce S) →g
      ((G.induce alive).induce S) := {
    toFun := id
    map_rel' := by intro u v h; exact h.1 }
  have hconn : ((G.induce alive).induce S).Connected :=
    hconnK.map forget (fun v => ⟨v,rfl⟩)
  have hDH := hG.induce alive
  have hmodule : HiddenCircuits.DH.GraphModule (G.induce alive) S := by
    apply hDH.farthest_layer_module hc r k
    · intro v; rw [live_dist hG alive hc]; exact hmax v
    · exact hcurrent
    · exact hconn.preconnected
    · intro u hu v huv hv
      have hv' : G.dist r.val v.val=k := by rwa [live_dist hG alive hc] at hv
      exact C.mem_supp_of_adj_mem_supp hu ⟨huv,(hdepth u hu).trans hv'.symm⟩
  refine ⟨hmodule,?_⟩
  let f : (G.induce alive).induce S ↪g
      (G.induce alive).induce {v | (G.induce alive).dist r v=k} := {
    toFun x := ⟨x.val,hcurrent x.val x.property⟩
    inj' := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : {v:alive | (G.induce alive).dist r v=k} => z.val) he)
    map_rel_iff' := by intro x y; rfl }
  exact (hDH.layer_p4Free hc r k).of_embedding f

/-- Static original predecessor-cardinality order yields actual inclusion
minimality after every common alive restriction. -/
theorem live_predecessors_minimal [Finite V] (hG : DistanceHereditaryGraph G) (hcG : G.Connected)
    (alive : Set V) (hc : (G.induce alive).Connected) (r u : alive)
    (hpos : 0<G.dist r.val u.val)
    (hsize : ∀z:alive, G.dist r.val z.val=G.dist r.val u.val →
      (predecessors G r.val u.val).ncard≤(predecessors G r.val z.val).ncard) :
    ∀z:alive, (G.induce alive).dist r z=(G.induce alive).dist r u →
      predecessors (G.induce alive) r z ⊆ predecessors (G.induce alive) r u →
      predecessors (G.induce alive) r u ⊆ predecessors (G.induce alive) r z := by
  intro z hz hsub
  have hzOriginal : G.dist r.val z.val=G.dist r.val u.val := by
    simpa only [live_dist hG alive hc] using hz
  rcases hG.predecessors_laminar hcG r.val u.val z.val hzOriginal.symm with hd | hinc | hinc
  · have hzpos : 0<(G.induce alive).dist r z := by rw [live_dist hG alive hc,hzOriginal]; exact hpos
    obtain ⟨x,hx⟩ := predecessors_nonempty (hc r z) hzpos
    exact False.elim (Set.disjoint_left.mp hd
      ((live_predecessor_iff hG alive hc r u x).mp (hsub hx))
      ((live_predecessor_iff hG alive hc r z x).mp hx))
  · intro x hx
    exact (live_predecessor_iff hG alive hc r z x).mpr
      (hinc ((live_predecessor_iff hG alive hc r u x).mp hx))
  · have he := Set.eq_of_subset_of_ncard_le hinc (hsize z hzOriginal)
    intro x hx
    exact (live_predecessor_iff hG alive hc r z x).mpr
      (he.symm ▸ ((live_predecessor_iff hG alive hc r u x).mp hx))

/-- The scheduled predecessor block is an actual current cograph module. -/
theorem live_predecessors_module [Finite V] (hG : DistanceHereditaryGraph G) (hcG : G.Connected)
    (alive : Set V) (hc : (G.induce alive).Connected) (r u : alive)
    (hpos : 0<G.dist r.val u.val)
    (hsize : ∀z:alive, G.dist r.val z.val=G.dist r.val u.val →
      (predecessors G r.val u.val).ncard≤(predecessors G r.val z.val).ncard) :
    HiddenCircuits.DH.GraphModule (G.induce alive) (predecessors (G.induce alive) r u) ∧
      P4Free ((G.induce alive).induce (predecessors (G.induce alive) r u)) := by
  exact ⟨(hG.induce alive).minimal_predecessors_module hc r u
    (live_predecessors_minimal hG hcG alive hc r u hpos hsize),
    (hG.induce alive).predecessors_p4Free r u⟩

/-- Collapsing a nonempty predecessor set never removes the rooted component's
root or the scheduled child, including the depth-one singleton-root case. -/
lemma predecessor_module_survivors [DecidableEq V] (hc : G.Connected)
    {r u keep : V} {S : Finset V} (hS : (S : Set V)=predecessors G r u) (hk : keep∈S) :
    (r=keep ∨ r∉S) ∧ u∉S := by
  constructor
  · by_cases hr : r∈S
    · left
      have hrp : r∈predecessors G r u := hS ▸ hr
      have hkp : keep∈predecessors G r u := hS ▸ hk
      have hrd := hrp.2
      have hkd := hkp.2
      simp only [dist_self] at hrd
      exact (hc r keep).dist_eq_zero_iff.mp (by omega)
    · exact Or.inr hr
  · intro hu
    have hup : u∈predecessors G r u := hS ▸ hu
    exact hup.1.ne rfl

lemma predecessor_module_depth {r u : V} {S : Finset V}
    (hS : (S : Set V)=predecessors G r u) :
    ∀v∈S, G.dist r v+1=G.dist r u := by
  intro v hv
  exact (show v∈predecessors G r u from hS ▸ hv).2

/-- After the actual predecessor-module contraction there is literally one
remaining predecessor in the induced graph. -/
theorem predecessors_after_module_merge [DecidableEq V]
    (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    {r u keep : V} {S : Finset V} (hS : (S : Set V)=predecessors G r u)
    (hm : HiddenCircuits.DH.GraphModule G (S : Set V)) (hk : keep∈S)
    (r' u' : ModuleSurvivor S keep) (hr : r'.val=r) (hu : u'.val=u) :
    predecessors (G.induce {x | x=keep ∨ x∉S}) r' u' = {moduleKeep S keep} := by
  have hconn := hm.connected_moduleDelete hk hc
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · intro hx
    have hp := (live_predecessor_iff hG _ hconn r' u' x).mp hx
    rw [hr,hu,←hS] at hp
    have he : x.val=keep := x.property.resolve_right (not_not.mpr hp)
    exact Subtype.ext he
  · intro hx
    subst x
    apply (live_predecessor_iff hG _ hconn r' u' (moduleKeep S keep)).mpr
    change keep∈predecessors G r'.val u'.val
    rw [hr,hu,←hS]
    exact hk

/-- The next scheduled deletion after predecessor contraction is a genuine
pendant operation in the current literal induced graph. -/
theorem pendant_after_predecessor_merge [DecidableEq V]
    (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    {r u keep : V} {S : Finset V} (hS : (S : Set V)=predecessors G r u)
    (hm : HiddenCircuits.DH.GraphModule G (S : Set V)) (hk : keep∈S)
    (r' u' : ModuleSurvivor S keep) (hr : r'.val=r) (hu : u'.val=u)
    (hmax : ∀v, G.dist r v≤G.dist r u)
    (hind : ∀v, G.dist r v=G.dist r u → ¬G.Adj u v) :
    PendantPair (G.induce {x | x=keep ∨ x∉S}) (moduleKeep S keep) u' := by
  apply pendant_of_unique_predecessor (G.induce {x | x=keep ∨ x∉S}) r' u' (moduleKeep S keep) (G.dist r u)
  · rw [moduleDelete_dist hG hc hm hk,hr,hu]
  · intro v
    rw [moduleDelete_dist hG hc hm hk,hr]
    exact hmax v.val
  · intro v hv hadj
    rw [moduleDelete_dist hG hc hm hk,hr] at hv
    apply hind v.val hv
    change G.Adj u'.val v.val at hadj
    simpa only [hu] using hadj
  · exact predecessors_after_module_merge hG hc hS hm hk r' u' hr hu

/-- One remaining live vertex per original same-depth component is exactly the
independence condition needed before predecessor and pendant processing. -/
lemma independent_of_static_component_unique (depth : V → ℕ) (alive : Set V) (k : ℕ)
    (hunique : ∀a b:alive, depth a.val=k → depth b.val=k →
      (sameDepthGraph G depth).connectedComponentMk a.val=
        (sameDepthGraph G depth).connectedComponentMk b.val → a=b) :
    ∀a b:alive, depth a.val=k → depth b.val=k → ¬(G.induce alive).Adj a b := by
  intro a b ha hb hab
  have hsame : (sameDepthGraph G depth).Adj a.val b.val := ⟨hab,ha.trans hb.symm⟩
  exact hab.ne (hunique a b ha hb (ConnectedComponent.sound hsame.reachable))

end HiddenCircuits.DH.LayerSchedule
