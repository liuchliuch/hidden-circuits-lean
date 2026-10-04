import HiddenCircuits.DH.GraphClasses
import HiddenCircuits.DH.BagPartition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Semantic lemmas for distance-hereditary pruning.  No reduction sequence is
assumed in the definition of the graph class. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph homomorphism cannot increase the distance of reachable vertices. -/
lemma hom_dist_le (f : G →g H) {a b : V} (h : G.Reachable a b) :
    H.dist (f a) (f b) ≤ G.dist a b := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist
  simpa only [Walk.length_map,hp] using dist_le (p.map f)

/-- Isomorphisms preserve the actual graph metric. -/
lemma iso_dist_eq (f : G ≃g H) (a b : V) :
    H.dist (f a) (f b) = G.dist a b := by
  by_cases hr : G.Reachable a b
  · apply le_antisymm (hom_dist_le f.toHom hr)
    have hm := hom_dist_le f.symm.toHom (hr.map f.toHom)
    simpa using hm
  · have hr' : ¬ H.Reachable (f a) (f b) := by
      rwa [Iso.reachable_iff]
    rw [dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr),
      dist_eq_zero_iff_eq_or_not_reachable.mpr (Or.inr hr')]

/-- A graph embedding identifies its source with the subgraph on its image. -/
noncomputable def embeddingRangeIso (f : G ↪g H) :
    G ≃g H.induce (Set.range f) where
  toEquiv := Equiv.ofInjective f f.injective
  map_rel_iff' := by
    intro a b
    exact f.map_rel_iff

/-- Every connected induced embedding in a distance-hereditary graph is isometric. -/
theorem DistanceHereditaryGraph.embedding_dist {H : SimpleGraph W}
    (hH : DistanceHereditaryGraph H) (f : G ↪g H) (hc : G.Connected) (a b : V) :
    H.dist (f a) (f b) = G.dist a b := by
  let e := embeddingRangeIso f
  have hc' : (H.induce (Set.range f)).Connected := hc.map e.toHom e.toEquiv.surjective
  exact (hH (Set.range f) hc' (e a) (e b)).symm.trans (iso_dist_eq e a b)

/-- Flatten two nested induced vertex sets without changing any adjacency. -/
noncomputable def inducedImageIso (S : Set V) (T : Set S) :
    (G.induce S).induce T ≃g G.induce (Subtype.val '' T) where
  toEquiv := {
    toFun := fun x => ⟨x.val.val,⟨x.val,x.property,rfl⟩⟩
    invFun := fun x => ⟨Classical.choose x.property,(Classical.choose_spec x.property).1⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact (Classical.choose_spec (show x.val.val ∈ Subtype.val '' T from
        ⟨x.val,x.property,rfl⟩)).2
    right_inv := by
      intro x
      apply Subtype.ext
      exact (Classical.choose_spec x.property).2 }
  map_rel_iff' := by intro a b; rfl

/-- Distance heredity is preserved by arbitrary induced vertex deletion, including
when the surviving graph is disconnected. -/
theorem DistanceHereditaryGraph.induce (hG : DistanceHereditaryGraph G) (S : Set V) :
    DistanceHereditaryGraph (G.induce S) := by
  intro T hc a b
  let e := inducedImageIso (G := G) S T
  have hc' : (G.induce (Subtype.val '' T)).Connected := hc.map e.toHom e.toEquiv.surjective
  have hd : ((G.induce S).induce T).dist a b = G.dist a.val.val b.val.val := by
    exact (iso_dist_eq e a b).symm.trans (hG _ hc' (e a) (e b))
  let f : ((G.induce S).induce T) →g G.induce S := ⟨Subtype.val,fun h => h⟩
  let g : G.induce S →g G := ⟨Subtype.val,fun h => h⟩
  have h₁ := hom_dist_le f (hc a b)
  have h₂ := hom_dist_le g ((hc a b).map f)
  change (G.induce S).dist a.val b.val ≤ ((G.induce S).induce T).dist a b at h₁
  change G.dist a.val.val b.val.val ≤ (G.induce S).dist a.val b.val at h₂
  omega

/-- A connected induced set containing vertices at distance two contains a common
neighbor.  This is the separator property used in the laminar BFS proof. -/
theorem DistanceHereditaryGraph.commonNeighbor_mem (hG : DistanceHereditaryGraph G)
    {S : Set V} (hc : (G.induce S).Connected) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (hd : G.dist a b = 2) : ∃ c ∈ S, G.Adj a c ∧ G.Adj c b := by
  have hd' : (G.induce S).dist ⟨a,ha⟩ ⟨b,hb⟩ = 2 :=
    (hG S hc ⟨a,ha⟩ ⟨b,hb⟩).trans hd
  obtain ⟨c,hac,hcb⟩ := exists_commonNeighbor_of_dist_two hd'
  exact ⟨c.val,c.property,hac,hcb⟩

/-- Deleting every common neighbor separates a nonadjacent pair which has a
common neighbor, in any distance-hereditary graph. -/
theorem DistanceHereditaryGraph.separated_without_commonNeighbors
    (hG : DistanceHereditaryGraph G) {a b c : V}
    (hab : a ≠ b) (hnab : ¬G.Adj a b) (hac : G.Adj a c) (hcb : G.Adj c b) :
    ¬ (G.induce {x | ¬(G.Adj a x ∧ G.Adj x b)}).Reachable
      ⟨a,by simp⟩ ⟨b,by simp⟩ := by
  intro hr
  obtain ⟨p⟩ := hr
  let S : Set V := Subtype.val '' {x | x ∈ p.support}
  have hc₀ := p.connected_induce_support
  let e := inducedImageIso (G := G) {x | ¬(G.Adj a x ∧ G.Adj x b)} {x | x ∈ p.support}
  have hc : (G.induce S).Connected := hc₀.map e.toHom e.toEquiv.surjective
  have ha : a ∈ S := ⟨⟨a,by simp⟩,p.start_mem_support,rfl⟩
  have hb : b ∈ S := ⟨⟨b,by simp⟩,p.end_mem_support,rfl⟩
  have hle : G.dist a b ≤ 2 := by simpa using dist_le (hac.toWalk.append hcb.toWalk)
  have hlt := (hac.reachable.trans hcb.reachable).one_lt_dist_of_ne_of_not_adj hab hnab
  obtain ⟨d,hd,had,hdb⟩ := hG.commonNeighbor_mem hc ha hb (by omega)
  obtain ⟨d',hd',he⟩ := hd
  exact d'.property ⟨he ▸ had,he ▸ hdb⟩

/-- Distances are preserved even when the induced subgraph is disconnected,
provided that the specified two vertices remain connected. -/
theorem DistanceHereditaryGraph.induce_dist_of_reachable
    (hG : DistanceHereditaryGraph G) {S : Set V} {a b : S}
    (hr : (G.induce S).Reachable a b) :
    (G.induce S).dist a b = G.dist a.val b.val := by
  obtain ⟨p⟩ := hr
  let T : Set S := {x | x ∈ p.support}
  let a' : T := ⟨a,p.start_mem_support⟩
  let b' : T := ⟨b,p.end_mem_support⟩
  let f : ((G.induce S).induce T) ↪g G := {
    toFun := fun x => x.val.val
    inj' := by intro x y h; exact Subtype.ext (Subtype.ext h)
    map_rel_iff' := by intro x y; rfl }
  let g : ((G.induce S).induce T) →g G.induce S := ⟨Subtype.val,fun h => h⟩
  let incl : G.induce S →g G := ⟨Subtype.val,fun h => h⟩
  have hc := p.connected_induce_support
  have hd := hG.embedding_dist f hc a' b'
  have h₁ := hom_dist_le g (hc a' b')
  have h₂ := hom_dist_le incl p.reachable
  change G.dist a.val b.val = ((G.induce S).induce T).dist a' b' at hd
  change (G.induce S).dist a b ≤ ((G.induce S).induce T).dist a' b' at h₁
  exact le_antisymm (hd ▸ h₁) h₂

/-- On a shortest path ending in the layer before `v`, the only possible
neighbor of `v` is the path's final vertex. -/
lemma shortest_neighbor_only_at_end {r s v x : V} (p : G.Walk r s)
    (hp : p.length = G.dist r s) (hv : G.dist r s + 1 = G.dist r v)
    (hx : x ∈ p.support) (hax : G.Adj v x) : x = s := by
  classical
  let i := p.support.idxOf x
  have hi : i ≤ p.length := by
    have h := List.idxOf_lt_length_iff.mpr hx
    rw [Walk.length_support] at h
    exact Nat.le_of_lt_succ h
  have hxi : p.getVert i = x := p.getVert_support_idxOf hx
  have hd := shortest_segment_dist p hp 0 i (by omega) hi
  simp only [Walk.getVert_zero,Nat.sub_zero,hxi] at hd
  have hbound := hax.symm.reachable.dist_triangle_right r
  rw [dist_eq_one_iff_adj.mpr hax.symm] at hbound
  have hei : i = p.length := by omega
  rw [← hxi,hei,Walk.getVert_length]

/-- Any surviving connected route to a positive BFS layer contains a surviving
predecessor. This follows from semantic distance preservation, not a BFS axiom. -/
theorem DistanceHereditaryGraph.predecessor_mem
    (hG : DistanceHereditaryGraph G) {S : Set V} {r v : S}
    (hr : (G.induce S).Reachable r v) (hv : 0 < G.dist r.val v.val) :
    ∃ x ∈ S, G.Adj x v.val ∧ G.dist r.val x + 1 = G.dist r.val v.val := by
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  have hd := hG.induce_dist_of_reachable hr
  have hlen : p.length = G.dist r.val v.val := hp.trans hd
  let incl : G.induce S →g G := ⟨Subtype.val,fun h => h⟩
  have hm : (p.map incl).length = G.dist r.val v.val := by simpa using hlen
  have hseg := shortest_segment_dist (p.map incl) hm 0 (p.length-1) (by omega) (by simp)
  simp only [Walk.getVert_map,Walk.getVert_zero,Nat.sub_zero] at hseg
  refine ⟨p.penultimate.val,p.penultimate.property,?_,?_⟩
  · exact p.adj_penultimate (by simpa only [Walk.not_nil_iff_lt_length] using (hlen ▸ hv))
  · change G.dist r.val (p.getVert (p.length-1)).val + 1 = G.dist r.val v.val
    change G.dist r.val (p.getVert (p.length-1)).val = p.length-1 at hseg
    omega

/-- The predecessors of adjacent vertices in one BFS layer coincide. -/
theorem DistanceHereditaryGraph.adjacent_same_level_predecessors
    (hG : DistanceHereditaryGraph G) {r u v s : V}
    (hrs : G.Reachable r s) (huv : G.Adj u v)
    (hu : G.dist r s + 1 = G.dist r u) (hv : G.dist r u = G.dist r v)
    (hsu : G.Adj s u) : G.Adj s v := by
  by_contra hsv
  obtain ⟨p,hp⟩ := hrs.exists_walk_length_eq_dist
  let S : Set V := {x | ¬ (G.Adj x v ∧ G.dist r x + 1 = G.dist r v)}
  have hpath : ∀ x ∈ p.support, x ∈ S := by
    intro x hx hbad
    have he := shortest_neighbor_only_at_end p hp (hu.trans hv) hx hbad.1.symm
    exact hsv (he ▸ hbad.1)
  have huS : u ∈ S := by intro h; omega
  have hvS : v ∈ S := by simp [S]
  let q := (p.append hsu.toWalk).append huv.toWalk
  have hq : ∀ x ∈ q.support, x ∈ S := by
    intro x hx
    simp [q,Walk.support_append,SimpleGraph.Adj.toWalk] at hx
    rcases hx with hx | rfl | rfl
    · exact hpath x hx
    · exact huS
    · exact hvS
  obtain ⟨x,hx,hxv,hxd⟩ := hG.predecessor_mem (q.induce S hq).reachable (by change 0 < G.dist r v; omega)
  exact hx ⟨hxv,hxd⟩

/-- The previous-layer neighbors of a vertex in a rooted BFS layering. -/
def predecessors (G : SimpleGraph V) (r v : V) : Set V :=
  {x | G.Adj x v ∧ G.dist r x + 1 = G.dist r v}

/-- The predecessor sets of vertices in one BFS layer form a laminar family.
This is Lemma 2 of Uehara--Uno, proved from the semantic distance definition. -/
theorem DistanceHereditaryGraph.predecessors_laminar
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r u v : V)
    (hlevel : G.dist r u = G.dist r v) :
    Disjoint (predecessors G r u) (predecessors G r v) ∨
      predecessors G r u ⊆ predecessors G r v ∨
      predecessors G r v ⊆ predecessors G r u := by
  classical
  by_cases hadj : G.Adj u v
  · right; left
    intro x hx
    exact ⟨hG.adjacent_same_level_predecessors (hc r x) hadj hx.2 hlevel hx.1,
      hx.2.trans hlevel⟩
  by_cases hdis : Disjoint (predecessors G r u) (predecessors G r v)
  · exact Or.inl hdis
  by_cases hsub : predecessors G r u ⊆ predecessors G r v
  · exact Or.inr (Or.inl hsub)
  by_cases hsub' : predecessors G r v ⊆ predecessors G r u
  · exact Or.inr (Or.inr hsub')
  exfalso
  obtain ⟨c,hcu,hcv⟩ := Set.not_disjoint_iff.mp hdis
  obtain ⟨s,hs,hsnot⟩ := Set.not_subset.mp hsub
  obtain ⟨t,ht,htnot⟩ := Set.not_subset.mp hsub'
  have hsv : ¬ G.Adj s v := fun ha => hsnot ⟨ha,hs.2.trans hlevel⟩
  have htu : ¬ G.Adj t u := fun ha => htnot ⟨ha,ht.2.trans hlevel.symm⟩
  have huv : u ≠ v := by intro he; subst v; exact hsnot hs
  obtain ⟨p,hp⟩ := (hc r s).exists_walk_length_eq_dist
  obtain ⟨q,hq⟩ := (hc r t).exists_walk_length_eq_dist
  let S : Set V := {x | ¬ (G.Adj u x ∧ G.Adj x v)}
  have hpS : ∀ x ∈ p.support, x ∈ S := by
    intro x hx hbad
    have he := shortest_neighbor_only_at_end p hp hs.2 hx hbad.1
    exact hsv (he ▸ hbad.2)
  have hqS : ∀ x ∈ q.support, x ∈ S := by
    intro x hx hbad
    have he := shortest_neighbor_only_at_end q hq ht.2 hx hbad.2.symm
    exact htu (he ▸ hbad.1.symm)
  have huS : u ∈ S := by simp [S]
  have hvS : v ∈ S := by simp [S]
  have hsS := hpS s p.end_mem_support
  have htS := hqS t q.end_mem_support
  have hru := (p.induce S hpS).reachable
  have hrv := (q.induce S hqS).reachable
  have hus : (G.induce S).Adj ⟨u,huS⟩ ⟨s,hsS⟩ := hs.1.symm
  have htv : (G.induce S).Adj ⟨t,htS⟩ ⟨v,hvS⟩ := ht.1
  have hreach := hus.reachable.trans (hru.symm.trans (hrv.trans htv.reachable))
  exact hG.separated_without_commonNeighbors huv hadj hcu.1.symm hcv.1 hreach

/-- Within one connected component above a BFS cut, all vertices on its boundary
have identical neighbors in the preceding layer. -/
theorem DistanceHereditaryGraph.upper_component_predecessors_eq
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : V) (k : ℕ)
    {u v : {x : V | k ≤ G.dist r x}}
    (hu : G.dist r u.val = k) (hv : G.dist r v.val = k)
    (hr : (G.induce {x : V | k ≤ G.dist r x}).Reachable u v) :
    predecessors G r u.val = predecessors G r v.val := by
  have incl (u v : {x : V | k ≤ G.dist r x})
      (hu : G.dist r u.val = k) (hv : G.dist r v.val = k)
      (hr : (G.induce {x : V | k ≤ G.dist r x}).Reachable u v) :
      predecessors G r u.val ⊆ predecessors G r v.val := by
    intro s hs
    refine ⟨?_,by have := hs.2; omega⟩
    by_contra hsv
    obtain ⟨p,hp⟩ := (hc r s).exists_walk_length_eq_dist
    obtain ⟨q⟩ := hr
    let S : Set V := {x | ¬ (G.Adj x v.val ∧ G.dist r x + 1 = G.dist r v.val)}
    have hpS : ∀ x ∈ p.support, x ∈ S := by
      intro x hx hbad
      have he := shortest_neighbor_only_at_end p hp (by have := hs.2; omega) hx hbad.1.symm
      exact hsv (he ▸ hbad.1)
    have hupper : ∀ x : {x : V | k ≤ G.dist r x}, x.val ∈ S := by
      intro x hbad
      have hx : k ≤ G.dist r x.val := x.property
      have hxv : G.dist r x.val + 1 = G.dist r v.val := hbad.2
      omega
    let incl : (G.induce {x : V | k ≤ G.dist r x}) →g G.induce S := {
      toFun x := ⟨x.val,hupper x⟩
      map_rel' := by intro a b h; exact h }
    have hsu : (G.induce S).Adj ⟨s,hpS s p.end_mem_support⟩ ⟨u.val,hupper u⟩ := hs.1
    have hroute := (p.induce S hpS).reachable.trans
      (hsu.reachable.trans (q.map incl).reachable)
    obtain ⟨x,hx,hxv,hxd⟩ := hG.predecessor_mem hroute (by
      change 0 < G.dist r v.val
      have := hs.2
      omega)
    exact hx ⟨hxv,hxd⟩
  exact Set.Subset.antisymm (incl u v hu hv hr) (incl v u hv hu hr.symm)

/-- An ordinary induced-P4 exclusion, independent of any decomposition. -/
def P4Free (G : SimpleGraph V) : Prop := IsEmpty (pathGraph 4 ↪g G)

lemma P4Free.of_embedding (hG : P4Free G) (f : H ↪g G) : P4Free H :=
  ⟨fun p => hG.false (p.trans f)⟩

lemma P4Free.induce (hG : P4Free G) (S : Set V) : P4Free (G.induce S) :=
  hG.of_embedding (Embedding.induce S)

lemma pathFour_endpoint_dist : (pathGraph 4).dist 0 3 = 3 := by
  have h01 : (pathGraph 4).Adj 0 1 := by rw [pathGraph_adj]; decide
  have h12 : (pathGraph 4).Adj 1 2 := by rw [pathGraph_adj]; decide
  have h23 : (pathGraph 4).Adj 2 3 := by rw [pathGraph_adj]; decide
  have hle : (pathGraph 4).dist 0 3 ≤ 3 := by
    simpa using dist_le ((h01.toWalk.append h12.toWalk).append h23.toWalk)
  have hgt := (pathGraph_connected 3).one_lt_dist_of_ne_of_not_adj
    (u := 0) (v := 3) (by decide) (by rw [pathGraph_adj]; decide)
  change 1 < (pathGraph 4).dist 0 3 at hgt
  by_contra hne
  have hd : (pathGraph 4).dist 0 3 = 2 := by omega
  obtain ⟨x,hx0,hx3⟩ := exists_commonNeighbor_of_dist_two hd
  fin_cases x <;> simp_all [pathGraph_adj]

/-- No induced four-vertex path in a distance-hereditary graph can have a
common neighbor of its endpoints. -/
lemma DistanceHereditaryGraph.inducedP4_no_commonNeighbor
    (hG : DistanceHereditaryGraph G) (f : pathGraph 4 ↪g G) (c : V)
    (h0 : G.Adj (f 0) c) (h3 : G.Adj c (f 3)) : False := by
  have hd := hG.embedding_dist f (pathGraph_connected 3) 0 3
  rw [pathFour_endpoint_dist] at hd
  have hle : G.dist (f 0) (f 3) ≤ 2 := by
    simpa using dist_le (h0.toWalk.append h3.toWalk)
  omega

/-- Every open neighborhood of a distance-hereditary graph is P4-free. -/
theorem DistanceHereditaryGraph.neighborhood_p4Free
    (hG : DistanceHereditaryGraph G) (c : V) : P4Free (G.induce (G.neighborSet c)) := by
  refine ⟨fun f => ?_⟩
  let f' : pathGraph 4 ↪g G := f.trans (Embedding.induce (G.neighborSet c))
  exact hG.inducedP4_no_commonNeighbor f' c (f 0).property.symm (f 3).property

/-- A positive-layer vertex has a predecessor on a shortest path. -/
lemma predecessors_nonempty {r v : V} (hr : G.Reachable r v)
    (hv : 0 < G.dist r v) : (predecessors G r v).Nonempty := by
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  have hnotnil : ¬p.Nil := by simpa only [Walk.not_nil_iff_lt_length,hp] using hv
  refine ⟨p.penultimate,p.adj_penultimate hnotnil,?_⟩
  have hd := shortest_segment_dist p hp 0 (p.length-1) (by omega) (by omega)
  simp only [Walk.getVert_zero,Nat.sub_zero] at hd
  change G.dist r (p.getVert (p.length-1)) + 1 = G.dist r v
  omega

/-- Each individual BFS layer of a distance-hereditary graph is P4-free. -/
theorem DistanceHereditaryGraph.layer_p4Free
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : V) (k : ℕ) :
    P4Free (G.induce {x | G.dist r x = k}) := by
  refine ⟨fun f => ?_⟩
  let e : pathGraph 4 ↪g G := f.trans (Embedding.induce {x | G.dist r x = k})
  have he (i : Fin 4) : G.dist r (e i) = k := (f i).property
  have he0 := he 0
  have he1 := he 1
  have he2 := he 2
  have he3 := he 3
  have hpos : 0 < k := by
    by_contra hn
    have h0 : e 0 = r := ((hc r (e 0)).dist_eq_zero_iff.mp (by omega)).symm
    have h1 : e 1 = r := ((hc r (e 1)).dist_eq_zero_iff.mp (by omega)).symm
    have := e.injective (h0.trans h1.symm)
    norm_num at this
  obtain ⟨s,hs⟩ := predecessors_nonempty (hc r (e 0)) (by omega)
  have hadj (a b : Fin 4) (h : (pathGraph 4).Adj a b) : G.Adj (e a) (e b) := e.map_rel_iff.mpr h
  have hs1 : G.Adj s (e 1) := hG.adjacent_same_level_predecessors (hc r s)
    (hadj 0 1 (by rw [pathGraph_adj]; decide)) hs.2 ((he 0).trans (he 1).symm) hs.1
  have hs2 : G.Adj s (e 2) := hG.adjacent_same_level_predecessors (hc r s)
    (hadj 1 2 (by rw [pathGraph_adj]; decide)) (by have := hs.2; omega)
    ((he 1).trans (he 2).symm) hs1
  have hs3 : G.Adj s (e 3) := hG.adjacent_same_level_predecessors (hc r s)
    (hadj 2 3 (by rw [pathGraph_adj]; decide)) (by have := hs.2; omega)
    ((he 2).trans (he 3).symm) hs2
  exact hG.inducedP4_no_commonNeighbor e s hs.1.symm hs3

/-- A module has a uniform adjacency pattern to all vertices outside it. -/
def GraphModule (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ∀ x ∉ S, (G.Adj u x ↔ G.Adj v x)

/-- Twins inside a module are genuine twins in the original graph. -/
lemma TwinPair.of_induce_module {S : Set V} (hm : GraphModule G S)
    {u v : S} (ht : TwinPair (G.induce S) u v) : TwinPair G u.val v.val where
  distinct := fun h => ht.distinct (Subtype.ext h)
  external x hxu hxv := by
    by_cases hx : x ∈ S
    · exact ht.external ⟨x,hx⟩ (fun h => hxu (congrArg Subtype.val h))
        (fun h => hxv (congrArg Subtype.val h))
    · exact hm v.val v.property u.val u.property x hx

/-- A connected component of the farthest BFS layer is a module.  The `closed`
condition is exactly closure under edges within that layer. -/
theorem DistanceHereditaryGraph.farthest_layer_module
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : V) (k : ℕ)
    (hmax : ∀ x, G.dist r x ≤ k) {S : Set V}
    (hS : ∀ x ∈ S, G.dist r x = k) (hconn : (G.induce S).Preconnected)
    (hclosed : ∀ u ∈ S, ∀ x, G.Adj u x → G.dist r x = k → x ∈ S) :
    GraphModule G S := by
  have forward (u : V) (hu : u ∈ S) (v : V) (hv : v ∈ S)
      (x : V) (hx : x ∉ S) (hux : G.Adj u x) : G.Adj v x := by
    have hxu : G.dist r x + 1 = G.dist r u := by
      have hneq : G.dist r x ≠ k := fun he => hx (hclosed u hu x hux he)
      have hbound := hmax x
      have hdiff := hux.diff_dist_adj (u := r)
      have hueq := hS u hu
      omega
    let e : G.induce S →g G.induce {y | k ≤ G.dist r y} := {
      toFun y := ⟨y.val,by change k ≤ G.dist r y.val; rw [hS y.val y.property]⟩
      map_rel' := by intro a b h; exact h }
    have hr := (hconn ⟨u,hu⟩ ⟨v,hv⟩).map e
    have he := hG.upper_component_predecessors_eq hc r k
      (u := e ⟨u,hu⟩) (v := e ⟨v,hv⟩) (hS u hu) (hS v hv) hr
    have hpred : x ∈ predecessors G r u := ⟨hux.symm,hxu⟩
    have hpred' : x ∈ predecessors G r v := he ▸ hpred
    exact hpred'.1.symm
  intro u hu v hv x hx
  exact ⟨forward u hu v hv x hx,forward v hv u hu x hx⟩

/-- A chordless three-edge route cannot coexist with a two-edge shortcut. -/
lemma DistanceHereditaryGraph.no_three_edge_shortcut
    (hG : DistanceHereditaryGraph G) {a b c d z : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬G.Adj a c) (had : ¬G.Adj a d) (hbd : ¬G.Adj b d)
    (haz : G.Adj a z) (hzd : G.Adj z d) : False := by
  let S : Set V := {x | ¬(G.Adj a x ∧ G.Adj x d)}
  have ha : a ∈ S := by simp [S]
  have hb : b ∈ S := fun h => hbd h.2
  have hc : c ∈ S := fun h => hac h.1
  have hd : d ∈ S := by simp [S]
  have hab' : (G.induce S).Adj ⟨a,ha⟩ ⟨b,hb⟩ := hab
  have hbc' : (G.induce S).Adj ⟨b,hb⟩ ⟨c,hc⟩ := hbc
  have hcd' : (G.induce S).Adj ⟨c,hc⟩ ⟨d,hd⟩ := hcd
  have hne : a ≠ d := by intro he; exact hbd (he ▸ hab.symm)
  exact hG.separated_without_commonNeighbors hne had haz hzd
    (hab'.reachable.trans (hbc'.reachable.trans hcd'.reachable))

/-- Two vertices in the preceding layer attached to a common successor have
identical predecessor sets of their own. -/
theorem DistanceHereditaryGraph.common_successor_predecessors_eq
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : V) {u v w : V}
    (hv : v ∈ predecessors G r u) (hw : w ∈ predecessors G r u) :
    predecessors G r v = predecessors G r w := by
  let S : Set V := {x | G.dist r v ≤ G.dist r x}
  have hvS : v ∈ S := by simp [S]
  have huS : u ∈ S := by change G.dist r v ≤ G.dist r u; have := hv.2; omega
  have hwS : w ∈ S := by change G.dist r v ≤ G.dist r w; have := hv.2; have := hw.2; omega
  have hvu : (G.induce S).Adj ⟨v,hvS⟩ ⟨u,huS⟩ := hv.1
  have huw : (G.induce S).Adj ⟨u,huS⟩ ⟨w,hwS⟩ := hw.1.symm
  exact hG.upper_component_predecessors_eq hc r (G.dist r v) rfl
    (by change G.dist r w = G.dist r v; have := hv.2; have := hw.2; omega)
    (hvu.reachable.trans huw.reachable)

/-- An inclusion-minimal predecessor set among the vertices of a fixed BFS
layer is a module in the entire graph. -/
theorem DistanceHereditaryGraph.minimal_predecessors_module
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r u : V)
    (hmin : ∀ z, G.dist r z = G.dist r u →
      predecessors G r z ⊆ predecessors G r u →
      predecessors G r u ⊆ predecessors G r z) :
    GraphModule G (predecessors G r u) := by
  have forward (v : V) (hv : v ∈ predecessors G r u)
      (w : V) (hw : w ∈ predecessors G r u)
      (x : V) (hx : x ∉ predecessors G r u) (hvx : G.Adj v x) : G.Adj w x := by
    have hvlevel := hv.2
    have hwlevel := hw.2
    have hvwlevel : G.dist r v = G.dist r w := by omega
    by_cases htop : G.dist r x = G.dist r u
    · have hvx' : v ∈ predecessors G r x := ⟨hvx,by omega⟩
      have hsub : predecessors G r u ⊆ predecessors G r x := by
        rcases hG.predecessors_laminar hc r u x htop.symm with hd | h | h
        · exact False.elim ((Set.disjoint_left.mp hd) hv hvx')
        · exact h
        · exact hmin x htop h
      exact (hsub hw).1
    have hpred := hG.common_successor_predecessors_eq hc r hv hw
    by_cases hsame : G.dist r x = G.dist r v
    · by_contra hwx
      have hux : ¬ G.Adj u x := fun ha => hx ⟨ha.symm,by omega⟩
      have hvw : v ≠ w := by intro he; exact hwx (he ▸ hvx)
      have hpos : 0 < G.dist r v := by
        by_contra hn
        have hvr : r = v := (hc r v).dist_eq_zero_iff.mp (by omega)
        have hwr : r = w := (hc r w).dist_eq_zero_iff.mp (by omega)
        exact hvw (hvr.symm.trans hwr)
      obtain ⟨t,ht⟩ := predecessors_nonempty (hc r v) hpos
      have htw : G.Adj t w := (show t ∈ predecessors G r w from hpred ▸ ht).1
      have htx : G.Adj t x := hG.adjacent_same_level_predecessors
        (hc r t) hvx ht.2 hsame.symm ht.1
      have hut : ¬ G.Adj u t := by
        intro ha
        have hh := ha.diff_dist_adj (u := r)
        have htlevel := ht.2
        omega
      exact hG.no_three_edge_shortcut hw.1.symm htw.symm htx hut hux hwx hv.1.symm hvx
    · have hxlevel : G.dist r x + 1 = G.dist r v := by
        have hh := hvx.diff_dist_adj (u := r)
        omega
      have hxpred : x ∈ predecessors G r v := ⟨hvx.symm,hxlevel⟩
      exact (show x ∈ predecessors G r w from hpred ▸ hxpred).1.symm
  intro v hv w hw x hx
  exact ⟨forward v hv w hw x hx,forward w hw v hv x hx⟩

end HiddenCircuits.DH
