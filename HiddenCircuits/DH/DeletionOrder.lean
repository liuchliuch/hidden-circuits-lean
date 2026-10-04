import HiddenCircuits.DH.BreadthFirst

/-! Actual pendant/twin deletion preserves graph distances and BFS-order structure. -/
namespace HiddenCircuits.DH
open SimpleGraph
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A vertex map which sends edges to paths preserves reachability, allowing an
edge to collapse to a single vertex. -/
lemma reachable_map_weak (f : V → W)
    (hf : ∀ a b, G.Adj a b → H.Reachable (f a) (f b))
    {a b : V} (hr : G.Reachable a b) : H.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Reachable.refl _
  | cons h p ih => exact (hf _ _ h).trans ih

/-- Removing one member of a twin pair preserves connectivity. -/
theorem TwinPair.connected_delete {u v : V} (ht : TwinPair G u v) (hc : G.Connected) :
    (G.induce {x | x ≠ v}).Connected := by
  let f := mergeRep u v ht.distinct
  have hf : ∀ a b, G.Adj a b → (G.induce {x | x ≠ v}).Reachable (f a) (f b) := by
    intro a b hab
    by_cases he : f a = f b
    · rw [he]
    · have ha : (G.induce {x | x ≠ v}).Adj (f a) (f b) := (ht.adj_merge a b he).mp hab
      exact ha.reachable
  haveI : Nonempty {x : V | x ≠ v} := ⟨⟨u,ht.distinct⟩⟩
  constructor
  intro a b
  have h := reachable_map_weak f hf (hc a.val b.val)
  simpa only [f,mergeRep_surviving u v a.val ht.distinct a.property,
    mergeRep_surviving u v b.val ht.distinct b.property] using h

/-- Removing a pendant vertex preserves connectivity. -/
theorem PendantPair.connected_delete {u v : V} (hp : PendantPair G u v) (hc : G.Connected) :
    (G.induce {x | x ≠ v}).Connected := by
  let f := mergeRep u v hp.distinct
  have hf : ∀ a b, G.Adj a b → (G.induce {x | x ≠ v}).Reachable (f a) (f b) := by
    intro a b hab
    by_cases he : f a = f b
    · rw [he]
    · have ha : (G.induce {x | x ≠ v}).Adj (f a) (f b) := ((hp.adj_merge a b he).mp hab).2.2
      exact ha.reachable
  haveI : Nonempty {x : V | x ≠ v} := ⟨⟨u,hp.distinct⟩⟩
  constructor
  intro a b
  have h := reachable_map_weak f hf (hc a.val b.val)
  simpa only [f,mergeRep_surviving u v a.val hp.distinct a.property,
    mergeRep_surviving u v b.val hp.distinct b.property] using h

/-- A pendant's distance to every other vertex is one plus its neighbor's distance. -/
theorem PendantPair.dist_from_leaf {u v : V} (hp : PendantPair G u v) (hc : G.Connected)
    (a : V) (ha : a ≠ v) : G.dist v a = G.dist u a+1 := by
  obtain ⟨p,hpdist⟩ := hc.exists_walk_length_eq_dist v a
  have hpn : ¬p.Nil := p.not_nil_of_ne ha.symm
  have hpu : p.snd = u := hp.unique p.snd (p.adj_snd hpn)
  have htail := dist_le p.tail
  have htail' : G.dist u a ≤ p.tail.length := by simpa only [hpu] using htail
  have hlen := p.length_tail_add_one hpn
  have hbound := hc.dist_triangle (u := v) (v := u) (w := a)
  rw [dist_eq_one_iff_adj.mpr hp.adjacent] at hbound
  omega

lemma PendantPair.leaf_not_predecessor {u v r a : V} (hp : PendantPair G u v)
    (hc : G.Connected) (hr : r ≠ v) : v ∉ predecessors G r a := by
  intro hv
  have ha : a = u := hp.unique a hv.1
  have hd := hp.dist_from_leaf hc r hr
  rw [G.dist_comm (u := v) (v := r),G.dist_comm (u := u) (v := r)] at hd
  have hpred := hv.2
  subst a
  omega

lemma TwinPair.predecessor_proxy {u v r a : V} (ht : TwinPair G u v)
    (hru : r ≠ u) (hrv : r ≠ v) (hav : a ≠ v) :
    v ∈ predecessors G r a ↔ u ∈ predecessors G r a := by
  have hd := ht.dist_eq_of_root_other r hru hrv
  by_cases hau : a = u
  · subst a
    simp only [predecessors,Set.mem_setOf_eq]
    constructor
    · intro h; have := h.2; omega
    · intro h; exact (h.1.ne rfl).elim
  · constructor
    · intro h
      exact ⟨(ht.external a hau hav).mp h.1,by have := h.2; omega⟩
    · intro h
      exact ⟨(ht.external a hau hav).mpr h.1,by have := h.2; omega⟩

lemma TwinPair.root_twin_not_predecessor {u v a : V} (ht : TwinPair G u v)
    (hc : G.Connected) (hav : a ≠ v) : v ∉ predecessors G u a := by
  intro h
  have hp := h.2
  by_cases hau : a = u
  · subst a; simp only [dist_self] at hp; omega
  · have hua := (ht.external a hau hav).mp h.1
    have hd : G.dist u a = 1 := dist_eq_one_iff_adj.mpr hua
    have huv : 0 < G.dist u v := hc.pos_dist_of_ne ht.distinct
    omega

/-- Exact restriction of predecessor membership when the root survives. -/
lemma predecessors_delete_iff {v : V} (hG : DistanceHereditaryGraph G)
    (hc : (G.induce {x | x ≠ v}).Connected) (r a x : {x : V | x ≠ v}) :
    x ∈ predecessors (G.induce {x | x ≠ v}) r a ↔ x.val ∈ predecessors G r.val a.val := by
  have hx := hG _ hc r x
  have ha := hG _ hc r a
  change (G.Adj x.val a.val ∧ (G.induce {x | x ≠ v}).dist r x+1 =
    (G.induce {x | x ≠ v}).dist r a) ↔ _
  rw [hx,ha]
  rfl

/-- Re-rooting after deleting the root pendant shifts every surviving distance
by exactly one, and preserves predecessor membership after restriction. -/
lemma PendantPair.reroot_dist {u v : V} (hp : PendantPair G u v) (hc : G.Connected)
    (hG : DistanceHereditaryGraph G) (a : {x : V | x ≠ v}) :
    G.dist v a.val = (G.induce {x | x ≠ v}).dist ⟨u,hp.distinct⟩ a+1 := by
  rw [hp.dist_from_leaf hc a.val a.property,hG _ (hp.connected_delete hc)]

lemma PendantPair.reroot_predecessors {u v : V} (hp : PendantPair G u v) (hc : G.Connected)
    (hG : DistanceHereditaryGraph G) (a x : {x : V | x ≠ v}) :
    x ∈ predecessors (G.induce {x | x ≠ v}) ⟨u,hp.distinct⟩ a ↔
      x.val ∈ predecessors G v a.val := by
  have hx := hp.reroot_dist hc hG x
  have ha := hp.reroot_dist hc hG a
  change (G.Adj x.val a.val ∧ (G.induce {x | x ≠ v}).dist ⟨u,hp.distinct⟩ x+1 =
    (G.induce {x | x ≠ v}).dist ⟨u,hp.distinct⟩ a) ↔
      G.Adj x.val a.val ∧ G.dist v x.val+1 = G.dist v a.val
  exact and_congr_right (fun _ => by omega)

/-- A rank representation of L1--L3, suitable for retaining the same numeric
alphabet order while vertices are deleted. -/
structure LevelRank (G : SimpleGraph V) (r : V) (rank : V → ℕ) : Prop where
  injective : Function.Injective rank
  level_order : ∀ u v, G.dist r u < G.dist r v → rank u < rank v
  inclusion_order : ∀ u v, G.dist r u = G.dist r v →
    predecessors G r v ⊂ predecessors G r u → rank u < rank v
  equal_contiguous : ∀ u v w, rank u < rank v → rank v < rank w →
    G.dist r u = G.dist r w → predecessors G r u = predecessors G r w →
    predecessors G r v = predecessors G r u

lemma restrict_subset_iff_absent (v : V) (A B : Set V) (ha : v ∉ A) :
    ({x : {x : V | x ≠ v} | x.val ∈ A} ⊆ {x : {x : V | x ≠ v} | x.val ∈ B}) ↔ A ⊆ B := by
  constructor
  · intro h x hx
    have hxv : x ≠ v := fun he => ha (he ▸ hx)
    exact h (show (⟨x,hxv⟩ : {x : V | x ≠ v}) ∈ {x | x.val ∈ A} from hx)
  · intro h x hx
    exact h hx

lemma restrict_subset_iff_proxy (u v : V) (huv : u ≠ v) (A B : Set V)
    (ha : v ∈ A ↔ u ∈ A) (hb : v ∈ B ↔ u ∈ B) :
    ({x : {x : V | x ≠ v} | x.val ∈ A} ⊆ {x : {x : V | x ≠ v} | x.val ∈ B}) ↔ A ⊆ B := by
  constructor
  · intro h x hx
    by_cases hxv : x = v
    · subst x
      exact hb.mpr (h (show (⟨u,huv⟩ : {x : V | x ≠ v}) ∈ {x | x.val ∈ A} from ha.mp hx))
    · exact h (show (⟨x,hxv⟩ : {x : V | x ≠ v}) ∈ {x | x.val ∈ A} from hx)
  · intro h x hx
    exact h hx

lemma predecessors_delete_eq {v : V} (hG : DistanceHereditaryGraph G)
    (hc : (G.induce {x | x ≠ v}).Connected) (r a : {x : V | x ≠ v}) :
    predecessors (G.induce {x | x ≠ v}) r a = {x | x.val ∈ predecessors G r.val a.val} := by
  ext x
  exact predecessors_delete_iff hG hc r a x

/-- Order transport uses proved preservation of the actual predecessor inclusion
relation, not a new sorting or relabeling certificate. -/
theorem LevelRank.delete_of_comparisons {r v : V} {rank : V → ℕ}
    (ho : LevelRank G r rank) (hG : DistanceHereditaryGraph G) (hr : r ≠ v)
    (hc : (G.induce {x | x ≠ v}).Connected)
    (hcompare : ∀ a b : {x : V | x ≠ v},
      predecessors (G.induce {x | x ≠ v}) ⟨r,hr⟩ a ⊆
        predecessors (G.induce {x | x ≠ v}) ⟨r,hr⟩ b ↔
      predecessors G r a.val ⊆ predecessors G r b.val) :
    LevelRank (G.induce {x | x ≠ v}) ⟨r,hr⟩ (fun x => rank x.val) := by
  have heq (a b : {x : V | x ≠ v}) :
      predecessors (G.induce {x | x ≠ v}) ⟨r,hr⟩ a =
        predecessors (G.induce {x | x ≠ v}) ⟨r,hr⟩ b ↔
      predecessors G r a.val = predecessors G r b.val := by
    constructor
    · intro h
      exact Set.Subset.antisymm ((hcompare a b).mp h.subset) ((hcompare b a).mp h.symm.subset)
    · intro h
      exact Set.Subset.antisymm ((hcompare a b).mpr h.subset) ((hcompare b a).mpr h.symm.subset)
  refine ⟨fun a b h => Subtype.ext (ho.injective h),?_,?_,?_⟩
  · intro a b hab
    have ha := hG _ hc ⟨r,hr⟩ a
    have hb := hG _ hc ⟨r,hr⟩ b
    dsimp only at ha hb
    exact ho.level_order a.val b.val (by omega)
  · intro a b hd hs
    have ha := hG _ hc ⟨r,hr⟩ a
    have hb := hG _ hc ⟨r,hr⟩ b
    dsimp only at ha hb
    apply ho.inclusion_order a.val b.val (by omega)
    rw [Set.ssubset_iff_subset_ne] at hs ⊢
    exact ⟨(hcompare b a).mp hs.1,fun he => hs.2 ((heq b a).mpr he)⟩
  · intro a b c hab hbc hd hs
    have ha := hG _ hc ⟨r,hr⟩ a
    have hc' := hG _ hc ⟨r,hr⟩ c
    dsimp only at ha hc'
    exact (heq b a).mpr (ho.equal_contiguous a.val b.val c.val hab hbc (by omega) ((heq a c).mp hs))

/-- L1--L3 survive every pendant deletion which retains the chosen root. -/
theorem PendantPair.preserves_levelRank {u v r : V} {rank : V → ℕ}
    (hp : PendantPair G u v) (hc : G.Connected) (hG : DistanceHereditaryGraph G)
    (ho : LevelRank G r rank) (hr : r ≠ v) :
    LevelRank (G.induce {x | x ≠ v}) ⟨r,hr⟩ (fun x => rank x.val) := by
  apply ho.delete_of_comparisons hG hr (hp.connected_delete hc)
  intro a b
  rw [predecessors_delete_eq hG (hp.connected_delete hc),
    predecessors_delete_eq hG (hp.connected_delete hc)]
  exact restrict_subset_iff_absent v _ _ (hp.leaf_not_predecessor hc hr)

/-- L1--L3 survive every twin deletion retaining the root. When the root is not
a twin, the surviving twin preserves every predecessor-set comparison. -/
theorem TwinPair.preserves_levelRank {u v r : V} {rank : V → ℕ}
    (ht : TwinPair G u v) (hc : G.Connected) (hG : DistanceHereditaryGraph G)
    (ho : LevelRank G r rank) (hr : r ≠ v) :
    LevelRank (G.induce {x | x ≠ v}) ⟨r,hr⟩ (fun x => rank x.val) := by
  apply ho.delete_of_comparisons hG hr (ht.connected_delete hc)
  intro a b
  rw [predecessors_delete_eq hG (ht.connected_delete hc),
    predecessors_delete_eq hG (ht.connected_delete hc)]
  by_cases hru : r = u
  · subst r
    exact restrict_subset_iff_absent v _ _ (ht.root_twin_not_predecessor hc a.property)
  · exact restrict_subset_iff_proxy u v ht.distinct _ _
      (ht.predecessor_proxy hru hr a.property) (ht.predecessor_proxy hru hr b.property)

lemma TwinPair.symm {u v : V} (ht : TwinPair G u v) : TwinPair G v u :=
  ⟨ht.distinct.symm,fun x hxv hxu => (ht.external x hxu hxv).symm⟩

lemma TwinPair.orient_away_from_root {u v : V} (ht : TwinPair G u v) (r : V) :
    ∃ a b, b ≠ r ∧ TwinPair G a b := by
  by_cases hv : v ≠ r
  · exact ⟨u,v,hv,ht⟩
  · have he : v = r := Classical.not_not.mp hv
    exact ⟨v,u,fun hu => ht.distinct (hu.trans he.symm),ht.symm⟩

/-- A connected nontrivial distance-hereditary graph always permits a pendant
or twin deletion which retains any designated root. This validates the
root-retaining optimization of the linear trie algorithm. -/
theorem DistanceHereditaryGraph.exists_reduction_away_from_root
    [Finite V] [Nontrivial V] (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : V) :
    ∃ u v : V, v ≠ r ∧ (PendantPair G u v ∨ TwinPair G u v) := by
  classical
  letI := Fintype.ofFinite V
  have hTw : ∀ S : Set V, S.Nontrivial → P4Free (G.induce S) →
      ∃ u v : S, TwinPair (G.induce S) u v := by
    intro S hS hfree
    letI : Nontrivial S := by
      obtain ⟨a,ha,b,hb,hab⟩ := hS
      exact ⟨⟨⟨a,ha⟩,⟨b,hb⟩,fun he => hab (congrArg Subtype.val he)⟩⟩
    exact hfree.exists_twins
  obtain ⟨f,hf,hfmax⟩ := Finset.univ.exists_max_image (fun v => G.dist r v) Finset.univ_nonempty
  let k := G.dist r f
  have hmax (x : V) : G.dist r x ≤ k := hfmax x (Finset.mem_univ x)
  have hpos : 0 < k := by
    obtain ⟨x,hxr⟩ := exists_ne r
    have hdist := hc.pos_dist_of_ne hxr.symm
    have := hmax x
    omega
  by_cases hedge : ∃ a b : V, G.dist r a = k ∧ G.dist r b = k ∧ G.Adj a b
  · obtain ⟨a,b,ha,hb,hab⟩ := hedge
    let L : Set V := {x | G.dist r x = k}
    let a' : L := ⟨a,ha⟩
    let b' : L := ⟨b,hb⟩
    let C := (G.induce L).connectedComponentMk a'
    let S := componentVertices L C
    have haC : a' ∈ C.supp := by simp [C,ConnectedComponent.mem_supp_iff]
    have hbC : b' ∈ C.supp := C.mem_supp_of_adj_mem_supp haC hab
    have haS : a ∈ S := ⟨a',haC,rfl⟩
    have hbS : b ∈ S := ⟨b',hbC,rfl⟩
    have hS : S.Nontrivial := ⟨a,haS,b,hbS,hab.ne⟩
    have hfree : P4Free (G.induce S) := (hG.layer_p4Free hc r k).of_embedding
      (G.induceHomOfLE (componentVertices_subset L C))
    have hmodule : GraphModule G S := hG.farthest_component_module hc r k hmax C
    obtain ⟨u,v,ht⟩ := hTw S hS hfree
    obtain ⟨a,b,hbr,hab⟩ := (ht.of_induce_module hmodule).orient_away_from_root r
    exact ⟨a,b,hbr,Or.inr hab⟩
  · obtain ⟨u,hu,hmin⟩ := exists_minimal_predecessors (G := G) r f
    have hulevel : G.dist r u = k := hu
    let S := predecessors G r u
    have hSne : S.Nonempty := predecessors_nonempty (hc r u) (by omega)
    by_cases hSn : S.Nontrivial
    · have hmodule : GraphModule G S := hG.minimal_predecessors_module hc r u hmin
      obtain ⟨v,w,ht⟩ := hTw S hSn (hG.predecessors_p4Free r u)
      obtain ⟨a,b,hbr,hab⟩ := (ht.of_induce_module hmodule).orient_away_from_root r
      exact ⟨a,b,hbr,Or.inr hab⟩
    · have hSs : S.Subsingleton := Set.not_nontrivial_iff.mp hSn
      obtain ⟨v,hv⟩ := hSne
      have hur : u ≠ r := by
        intro he
        rw [he,dist_self] at hulevel
        omega
      refine ⟨v,u,hur,Or.inl ⟨hv.1.symm,?_⟩⟩
      intro x hux
      have hx : x ∈ S := by
        refine ⟨hux.symm,?_⟩
        have hdiff := hux.diff_dist_adj (u := r)
        have hbound := hmax x
        have hxne : G.dist r x ≠ k := fun he => hedge ⟨u,x,hulevel,he,hux⟩
        omega
      exact hSs hx hv

/-- List positions of a constructed order satisfy the reusable deletion invariant. -/
theorem LevelOrdering.IsLevelwiseLaminar.toLevelRank {n : ℕ} {G : SimpleGraph (Fin n)}
    {r : Fin n} {vertices : List (Fin n)}
    (ho : LevelOrdering.IsLevelwiseLaminar G r vertices) :
    LevelRank G r (fun v => vertices.idxOf v) := by
  have hm (v : Fin n) : v ∈ vertices := ho.permutation.mem_iff.mpr (List.mem_finRange v)
  let ix (v : Fin n) : Fin vertices.length := ⟨vertices.idxOf v,List.idxOf_lt_length_iff.mpr (hm v)⟩
  have hget (v : Fin n) : vertices.get (ix v) = v := List.idxOf_get _
  have hinj : Function.Injective (fun v => vertices.idxOf v) :=
    fun u v h => (List.idxOf_inj (hm u)).mp h
  refine ⟨hinj,?_,?_,?_⟩
  · intro u v huv
    by_contra hn
    have hne : vertices.idxOf u ≠ vertices.idxOf v := by
      intro he
      have he' := hinj he
      subst v
      omega
    have hvi : ix v < ix u := by change vertices.idxOf v < vertices.idxOf u; omega
    have hdist := ho.level_order.rel_get_of_lt hvi
    simp only [hget] at hdist
    omega
  · intro u v hd hs
    have h := ho.inclusion_order (ix u) (ix v) (by simpa only [hget] using hd)
      (by simpa only [hget] using hs)
    exact h
  · intro u v w huv hvw hd hs
    have h := ho.equal_contiguous (ix u) (ix v) (ix w) huv hvw
      (by simpa only [hget] using hd) (by simpa only [hget] using hs)
    simpa only [hget] using h

namespace RankArray

/-- Install list positions in a real array, one write per vertex. -/
def write {n : ℕ} : List (Fin n) → ℕ → Vector ℕ n → Vector ℕ n × ℕ
  | [],_,ranks => (ranks,0)
  | v :: vs,k,ranks =>
      let q := write vs (k+1) (ranks.set v.val k)
      (q.1,q.2+3)

@[simp] lemma write_accesses {n : ℕ} (vertices : List (Fin n)) (k : ℕ) (ranks : Vector ℕ n) :
    (write vertices k ranks).2 = 3*vertices.length := by
  induction vertices generalizing k ranks <;> simp [write, *] <;> omega

lemma write_get {n : ℕ} (vertices : List (Fin n)) (hn : vertices.Nodup)
    (k : ℕ) (ranks : Vector ℕ n) (x : Fin n) :
    (write vertices k ranks).1[x.val] = if x ∈ vertices then k+vertices.idxOf x else ranks[x.val] := by
  induction vertices generalizing k ranks with
  | nil => simp [write]
  | cons v vs ih =>
    obtain ⟨hvn,hn⟩ := List.nodup_cons.mp hn
    rw [write,ih hn]
    by_cases he : x = v
    · subst v
      simp [hvn]
    · have hev : v.val ≠ x.val := fun h => he (Fin.ext h.symm)
      simp [he,hev,List.idxOf_cons_ne,eq_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Build a constant-time rank lookup table for a supplied vertex permutation. -/
def build {n : ℕ} (vertices : List (Fin n)) : Vector ℕ n × ℕ :=
  let q := write vertices 0 (Vector.replicate n 0)
  (q.1,q.2+n)

lemma build_get {n : ℕ} (vertices : List (Fin n)) (hp : vertices.Perm (List.finRange n)) (x : Fin n) :
    (build vertices).1[x.val] = vertices.idxOf x := by
  have hn : vertices.Nodup := hp.nodup_iff.mpr (List.nodup_finRange n)
  have hx : x ∈ vertices := hp.mem_iff.mpr (List.mem_finRange x)
  simp [build,write_get vertices hn, hx]

lemma build_accesses {n : ℕ} (vertices : List (Fin n)) (hp : vertices.Perm (List.finRange n)) :
    (build vertices).2 = 4*n := by
  have hl := hp.length_eq
  simp only [List.length_finRange] at hl
  simp [build,write_accesses,hl]
  omega

/-- The actually computed array satisfies all L1--L3 rank requirements. -/
theorem build_levelRank {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    (vertices : List (Fin n)) (ho : LevelOrdering.IsLevelwiseLaminar G r vertices) :
    LevelRank G r (fun v => (build vertices).1[v.val]) := by
  have he : (fun v : Fin n => (build vertices).1[v.val]) = (fun v => vertices.idxOf v) :=
    funext (build_get vertices ho.permutation)
  rw [he]
  exact ho.toLevelRank

structure RankedGraph (n : ℕ) where
  vertices : List (Fin n)
  ranks : Vector ℕ n
  accesses : ℕ

/-- Ordinary adjacency arrays yield both the levelwise order and its constant-time
rank lookup table, before trie preprocessing begins. -/
def construct {n : ℕ} (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (r : Fin n) : RankedGraph n :=
  let o := BreadthFirst.levelwiseOrder rows hn r
  let a := build o.vertices
  ⟨o.vertices,a.1,o.accesses+a.2⟩

/-- The constructed numeric order is ready for arbitrary many valid nonroot
pendant/twin deletions using the preservation theorems above. -/
theorem construct_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (r : Fin n) :
    LevelRank G r (fun v => (construct rows hn r).ranks[v.val]) ∧
      (construct rows hn r).vertices.Perm (List.finRange n) ∧
      (construct rows hn r).accesses ≤ 26*G.edgeFinset.card+57*n+14 := by
  have ho := BreadthFirst.levelwiseOrder_spec G hG hc rows hr hn r
  refine ⟨build_levelRank _ ho.1,ho.1.permutation,?_⟩
  have ha := build_accesses _ ho.1.permutation
  change (BreadthFirst.levelwiseOrder rows hn r).accesses+
    (build (BreadthFirst.levelwiseOrder rows hn r).vertices).2 ≤ _
  omega

end RankArray

end HiddenCircuits.DH
