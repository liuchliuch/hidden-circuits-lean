import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic

/-! Semantic graph classes used in Section 12. Distance heredity is defined by actual
distances in connected induced subgraphs, and quasi-chains by their bipartite cuts. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V W : Type*}

/-- The paper's definition, including arbitrary disconnected original graphs. -/
def DistanceHereditaryGraph (G : SimpleGraph V) : Prop :=
  ∀ (S : Set V), (G.induce S).Connected → ∀ (u v : S),
    (G.induce S).dist u v = G.dist u.val v.val

/-- Keep exactly the original edges crossing a vertex bipartition. -/
def cutGraph (G : SimpleGraph V) (L : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ((a ∈ L ∧ b ∉ L) ∨ (b ∈ L ∧ a ∉ L))
  symm := by intro a b h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

/-- Each connected component of a cut is a chain graph: same-side neighborhoods are nested. -/
def CutHasChainComponents (G : SimpleGraph V) (L : Set V) : Prop :=
  ∀ a b, (a ∈ L ↔ b ∈ L) → (cutGraph G L).Reachable a b →
    (∀ x, (cutGraph G L).Adj a x → (cutGraph G L).Adj b x) ∨
    (∀ x, (cutGraph G L).Adj b x → (cutGraph G L).Adj a x)

/-- Quasi-chain graphs in the paper's cut-based sense, with disjoint chain components allowed. -/
def QuasiChains (G : SimpleGraph V) : Prop := ∀ L : Set V, CutHasChainComponents G L

/-- Five distinct original vertices with a P5 bipartite cut; within-part edges are unrestricted. -/
structure PreP5Embedding (G : SimpleGraph V) where
  vertices : Fin 5 ↪ V
  edge01 : G.Adj (vertices 0) (vertices 1)
  edge12 : G.Adj (vertices 1) (vertices 2)
  edge23 : G.Adj (vertices 2) (vertices 3)
  edge34 : G.Adj (vertices 3) (vertices 4)
  nonedge03 : ¬G.Adj (vertices 0) (vertices 3)
  nonedge14 : ¬G.Adj (vertices 1) (vertices 4)

def PreP5Free (G : SimpleGraph V) : Prop := IsEmpty (PreP5Embedding G)

/-- This exclusion follows directly from the cut definition, without invoking a characterization. -/
theorem quasiChains_preP5Free {G : SimpleGraph V} (hG : QuasiChains G) : PreP5Free G := by
  refine ⟨fun p => ?_⟩
  let L : Set V := {x | x=p.vertices 0 ∨ x=p.vertices 2 ∨ x=p.vertices 4}
  have hl0 : p.vertices 0 ∈ L := by simp [L]
  have hl1 : p.vertices 1 ∉ L := by simp [L,p.vertices.injective.eq_iff]
  have hl2 : p.vertices 2 ∈ L := by simp [L]
  have hl3 : p.vertices 3 ∉ L := by simp [L,p.vertices.injective.eq_iff]
  have hl4 : p.vertices 4 ∈ L := by simp [L]
  have h01 : (cutGraph G L).Adj (p.vertices 0) (p.vertices 1) := ⟨p.edge01,Or.inl ⟨hl0,hl1⟩⟩
  have h12 : (cutGraph G L).Adj (p.vertices 1) (p.vertices 2) := ⟨p.edge12,Or.inr ⟨hl2,hl1⟩⟩
  have h23 : (cutGraph G L).Adj (p.vertices 2) (p.vertices 3) := ⟨p.edge23,Or.inl ⟨hl2,hl3⟩⟩
  have h34 : (cutGraph G L).Adj (p.vertices 3) (p.vertices 4) := ⟨p.edge34,Or.inr ⟨hl4,hl3⟩⟩
  have hr := h01.reachable.trans (h12.reachable.trans (h23.reachable.trans h34.reachable))
  rcases hG L _ _ (by simp only [hl0,hl4]) hr with h | h
  · exact p.nonedge14 (h _ h01).1.symm
  · exact p.nonedge03 (h _ h34.symm).1

/-- A pre-P5 in an induced subgraph remains the same forbidden cut in the original graph. -/
def PreP5Embedding.ofInduce {G : SimpleGraph V} {S : Set V}
    (p : PreP5Embedding (G.induce S)) : PreP5Embedding G where
  vertices := p.vertices.trans ⟨Subtype.val,Subtype.val_injective⟩
  edge01 := p.edge01
  edge12 := p.edge12
  edge23 := p.edge23
  edge34 := p.edge34
  nonedge03 := p.nonedge03
  nonedge14 := p.nonedge14

lemma PreP5Free.induce {G : SimpleGraph V} (h : PreP5Free G) (S : Set V) :
    PreP5Free (G.induce S) := ⟨fun p => h.false p.ofInduce⟩

/-- A shortest walk has the exact internal distances along all its subwalks. -/
lemma shortest_segment_dist {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (hp : p.length = G.dist a b) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j-i := by
  have hs := length_eq_dist_of_subwalk hp
    (((p.drop i).isSubwalk_take (j-i)).trans (p.isSubwalk_drop i))
  simp only [Walk.take_length,Walk.drop_length,Walk.drop_getVert] at hs
  rw [show i+(j-i)=j by omega, min_eq_left (by omega)] at hs
  exact hs.symm

/-- A shortest path of length four already supplies a forbidden pre-P5 cut. -/
theorem PreP5Free.shortest_length_le_three {G : SimpleGraph V} (h : PreP5Free G)
    {a b : V} (p : G.Walk a b) (hp : p.length = G.dist a b) : p.length ≤ 3 := by
  by_contra hlen
  have h4 : 4 ≤ p.length := by omega
  have hpath := p.isPath_of_length_eq_dist hp
  let e : Fin 5 ↪ V := ⟨fun i => p.getVert i.val,by
    intro i j he
    apply Fin.ext
    exact hpath.getVert_injOn (by dsimp; omega) (by dsimp; omega) he⟩
  have hadj (i : ℕ) (hi : i < 4) : G.Adj (p.getVert i) (p.getVert (i+1)) :=
    p.adj_getVert_succ (by omega)
  apply h.false
  exact {
    vertices := e
    edge01 := hadj 0 (by decide)
    edge12 := hadj 1 (by decide)
    edge23 := hadj 2 (by decide)
    edge34 := hadj 3 (by decide)
    nonedge03 := by
      intro ha
      have hdist := shortest_segment_dist p hp 0 3 (by omega) (by omega)
      have hone := (dist_eq_one_iff_adj).mpr ha
      change G.dist (p.getVert 0) (p.getVert 3)=1 at hone
      omega
    nonedge14 := by
      intro ha
      have hdist := shortest_segment_dist p hp 1 4 (by omega) (by omega)
      have hone := (dist_eq_one_iff_adj).mpr ha
      change G.dist (p.getVert 1) (p.getVert 4)=1 at hone
      omega }

/-- A length-three induced path cannot acquire a two-edge shortcut without a pre-P5. -/
lemma PreP5Free.noP4Shortcut {G : SimpleGraph V} (hG : PreP5Free G)
    (e : Fin 4 ↪ V) (h01 : G.Adj (e 0) (e 1)) (h12 : G.Adj (e 1) (e 2))
    (h23 : G.Adj (e 2) (e 3)) (h02 : ¬G.Adj (e 0) (e 2))
    (h13 : ¬G.Adj (e 1) (e 3)) (z : V) (haz : G.Adj (e 0) z)
    (hzd : G.Adj z (e 3)) : False := by
  have hz0 : z ≠ e 0 := haz.ne.symm
  have hz1 : z ≠ e 1 := by intro he; exact h13 (he ▸ hzd)
  have hz2 : z ≠ e 2 := by intro he; exact h02 (he ▸ haz)
  have hz3 : z ≠ e 3 := hzd.ne
  let f : Fin 5 → V := ![e 1,e 0,z,e 3,e 2]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f,e.injective.eq_iff,eq_comm]
  apply hG.false
  exact {
    vertices := ⟨f,hf⟩
    edge01 := h01.symm
    edge12 := haz
    edge23 := hzd
    edge34 := h23.symm
    nonedge03 := h13
    nonedge14 := h02 }

lemma exists_commonNeighbor_of_dist_two {G : SimpleGraph V} {a b : V}
    (h : G.dist a b = 2) : ∃ z, G.Adj a z ∧ G.Adj z b := by
  obtain ⟨p,hp⟩ := exists_walk_of_dist_ne_zero (G := G) (u := a) (v := b) (by omega)
  have hl : p.length = 2 := hp.trans h
  refine ⟨p.getVert 1,?_,?_⟩
  · simpa using p.adj_getVert_succ (i := 0) (by omega)
  · have hadj := p.adj_getVert_succ (i := 1) (by omega)
    simpa only [show (1 : ℕ)+1=p.length by omega,Walk.getVert_length] using hadj

/-- A graph with no induced pre-P5 preserves all connected induced-subgraph distances.
The proof only needs paths of length at most three and the explicit shortcut obstruction. -/
theorem preP5Free_distanceHereditary {G : SimpleGraph V} (hG : PreP5Free G) :
    DistanceHereditaryGraph G := by
  intro S hconn u v
  obtain ⟨p,hp⟩ := hconn.exists_walk_length_eq_dist u v
  have hlen := (hG.induce S).shortest_length_le_three p hp
  let incl : (G.induce S) →g G := ⟨Subtype.val,fun ha => ha⟩
  have hgle : G.dist u.val v.val ≤ p.length := by simpa using dist_le (p.map incl)
  have hreach : G.Reachable u.val v.val := (p.map incl).reachable
  by_cases huv : u=v
  · subst v
    simp
  · have hne : u.val ≠ v.val := fun he => huv (Subtype.ext he)
    have hpos := hreach.pos_dist_of_ne hne
    by_contra hneq
    have hlt : G.dist u.val v.val < (G.induce S).dist u v := by omega
    have hnotadj : ¬G.Adj u.val v.val := by
      intro hadj
      have hd : (G.induce S).dist u v = 1 := dist_eq_one_iff_adj.mpr hadj
      omega
    have hlower := hreach.one_lt_dist_of_ne_of_not_adj hne hnotadj
    have hp3 : p.length = 3 := by omega
    have hg2 : G.dist u.val v.val = 2 := by omega
    obtain ⟨z,huz,hzv⟩ := exists_commonNeighbor_of_dist_two hg2
    have hpath := p.isPath_of_length_eq_dist hp
    let e : Fin 4 ↪ V := ⟨fun i => (p.getVert i.val).val,by
      intro i j he
      apply Fin.ext
      exact hpath.getVert_injOn (by dsimp; omega) (by dsimp; omega) (Subtype.ext he)⟩
    have he0 : e 0 = u.val := by simp [e]
    have he3 : e 3 = v.val := by
      change (p.getVert 3).val = v.val
      rw [← hp3,Walk.getVert_length]
    have hadj (i : ℕ) (hi : i < 3) :
        G.Adj (p.getVert i).val (p.getVert (i+1)).val := p.adj_getVert_succ (by omega)
    have h02 : ¬G.Adj (e 0) (e 2) := by
      intro ha
      have hd := shortest_segment_dist p hp 0 2 (by omega) (by omega)
      have hone : (G.induce S).dist (p.getVert 0) (p.getVert 2)=1 := dist_eq_one_iff_adj.mpr ha
      omega
    have h13 : ¬G.Adj (e 1) (e 3) := by
      intro ha
      have hd := shortest_segment_dist p hp 1 3 (by omega) (by omega)
      have hone : (G.induce S).dist (p.getVert 1) (p.getVert 3)=1 := dist_eq_one_iff_adj.mpr ha
      omega
    exact hG.noP4Shortcut e (hadj 0 (by decide)) (hadj 1 (by decide))
      (hadj 2 (by decide)) h02 h13 z (he0 ▸ huz) (he3 ▸ hzv)

/-- The graph-class inclusion is derived from the paper's semantic definitions. -/
theorem quasiChains_distanceHereditary {G : SimpleGraph V} (hG : QuasiChains G) :
    DistanceHereditaryGraph G := preP5Free_distanceHereditary (quasiChains_preP5Free hG)

/-- Every forest is distance hereditary, by uniqueness of the actual simple paths. -/
theorem acyclic_distanceHereditary {G : SimpleGraph V} (hG : G.IsAcyclic) :
    DistanceHereditaryGraph G := by
  intro S hconn u v
  obtain ⟨p,hpath,hp⟩ := hconn.exists_path_of_dist u v
  let incl : (G.induce S) →g G := ⟨Subtype.val,fun ha => ha⟩
  have hmap : (p.map incl).IsPath := p.map_isPath_of_injective Subtype.val_injective hpath
  obtain ⟨q,hqpath,hq⟩ := (p.map incl).reachable.exists_path_of_dist
  have he := hG.path_unique ⟨p.map incl,hmap⟩ ⟨q,hqpath⟩
  have hl := congrArg (fun r : G.Path u.val v.val => r.val.length) he
  change (p.map incl).length = q.length at hl
  rw [Walk.length_map] at hl
  change q.length = G.dist u.val v.val at hq
  omega

/-- P5 supplies strictness: it is a tree but has its own non-chain cut. -/
theorem pathFive_distanceHereditary : DistanceHereditaryGraph (pathGraph 5) := by
  apply acyclic_distanceHereditary
  apply (isTree_iff_connected_and_card.mpr ?_).IsAcyclic
  refine ⟨pathGraph_connected 4,?_⟩
  classical
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← edgeFinset_card]
  have he : (pathGraph 5).edgeFinset =
      {s((0 : Fin 5),1),s((1 : Fin 5),2),s((2 : Fin 5),3),s((3 : Fin 5),4)} := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [mem_edgeFinset,mem_edgeSet,pathGraph_adj,Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff]
      fin_cases a <;> fin_cases b <;> decide
  rw [he]
  simp [Finset.card_insert_of_notMem,Sym2.eq_iff]

def pathFive_preP5 : PreP5Embedding (pathGraph 5) where
  vertices := Function.Embedding.refl _
  edge01 := by rw [pathGraph_adj]; decide
  edge12 := by rw [pathGraph_adj]; decide
  edge23 := by rw [pathGraph_adj]; decide
  edge34 := by rw [pathGraph_adj]; decide
  nonedge03 := by rw [pathGraph_adj]; decide
  nonedge14 := by rw [pathGraph_adj]; decide

theorem pathFive_not_quasiChains : ¬QuasiChains (pathGraph 5) :=
  fun h => (quasiChains_preP5Free h).false pathFive_preP5

/-- Inclusion and an explicit separating graph, with no forbidden-graph theorem assumed. -/
theorem quasiChains_strict_distanceHereditary :
    (∀ {V : Type} (G : SimpleGraph V), QuasiChains G → DistanceHereditaryGraph G) ∧
      DistanceHereditaryGraph (pathGraph 5) ∧ ¬QuasiChains (pathGraph 5) :=
  ⟨fun _ h => quasiChains_distanceHereditary h,pathFive_distanceHereditary,pathFive_not_quasiChains⟩

end HiddenCircuits.DH
