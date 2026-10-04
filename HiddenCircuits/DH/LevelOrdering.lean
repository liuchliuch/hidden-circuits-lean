import HiddenCircuits.DH.LinearBuckets
import HiddenCircuits.DH.PruningAutomorphisms

/-! A bounded-key radix construction of levelwise laminar orders.
The third key groups equal predecessor neighborhoods without relying on BFS tie breaking. -/
namespace HiddenCircuits.DH.LevelOrdering
open SimpleGraph

structure Keys (n : ℕ) where
  depth : Fin (n+1)
  size : Fin (n+1)
  anchor : Fin (n+1)

def Before {n : ℕ} (a b : Keys n) : Prop :=
  a.depth.val < b.depth.val ∨ a.depth.val = b.depth.val ∧
    (b.size.val < a.size.val ∨ b.size.val = a.size.val ∧ a.anchor.val ≤ b.anchor.val)

lemma Before.depth_le {n : ℕ} {a b : Keys n} (h : Before a b) : a.depth.val ≤ b.depth.val := by
  unfold Before at h
  omega

lemma Before.size_le {n : ℕ} {a b : Keys n} (h : Before a b)
    (hd : a.depth.val = b.depth.val) : b.size.val ≤ a.size.val := by
  unfold Before at h
  omega

lemma Before.anchor_le {n : ℕ} {a b : Keys n} (h : Before a b)
    (hd : a.depth.val = b.depth.val) (hs : a.size.val = b.size.val) :
    a.anchor.val ≤ b.anchor.val := by
  unfold Before at h
  omega

/-- Three actual bounded-key stable sorting passes over vertex labels. -/
def order {n : ℕ} (keys : Vector (Keys n) n) : List (Fin n) × ℕ :=
  let q := LinearBuckets.radix3 (fun v => keys[v.val].depth.rev) (fun v => keys[v.val].size)
    (fun v => keys[v.val].anchor.rev) (List.finRange n)
  (q.1,q.2+7*n)

lemma order_perm {n : ℕ} (keys : Vector (Keys n) n) : (order keys).1.Perm (List.finRange n) :=
  LinearBuckets.radix3_perm _ _ _ _

lemma order_sorted {n : ℕ} (keys : Vector (Keys n) n) :
    (order keys).1.Pairwise (fun u v => Before keys[u.val] keys[v.val]) := by
  have h := LinearBuckets.radix3_order (fun v : Fin n => keys[v.val].depth.rev)
    (fun v => keys[v.val].size) (fun v => keys[v.val].anchor.rev) (List.finRange n)
  apply h.imp
  intro u v huv
  simp only [Fin.rev_lt_rev,Fin.rev_inj,Fin.rev_le_rev] at huv
  change Before keys[u.val] keys[v.val]
  unfold Before
  rcases huv with h | ⟨hd,h⟩
  · exact Or.inl h
  · refine Or.inr ⟨congrArg Fin.val hd.symm,?_⟩
    rcases h with hs | ⟨hs,ha⟩
    · exact Or.inl hs
    · exact Or.inr ⟨congrArg Fin.val hs,ha⟩

lemma order_accesses {n : ℕ} (keys : Vector (Keys n) n) : (order keys).2 = 34*n+12 := by
  rw [order,LinearBuckets.radix3_accesses,List.length_finRange]
  omega

/-- Literal representation correctness of precomputed depth, size and anchor keys.
The anchor is a chosen member of each nonempty predecessor set, with equal sets
using the same member. A minimum-label scan establishes these fields. -/
structure KeySpec {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n)
    (keys : Vector (Keys n) n) : Prop where
  depth : ∀ v, keys[v.val].depth.val = G.dist r v
  size : ∀ v, keys[v.val].size.val = (predecessors G r v).ncard
  anchor_mem : ∀ v, 0 < G.dist r v →
    ∃ x ∈ predecessors G r v, x.val = keys[v.val].anchor.val
  anchor_congr : ∀ u v, predecessors G r u = predecessors G r v →
    keys[u.val].anchor = keys[v.val].anchor

/-- Equal keys determine equal neighborhoods, by the genuine BFS laminarity
lemma and finite-set cardinality, rather than a hash-injectivity assumption. -/
lemma KeySpec.predecessors_eq {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {keys : Vector (Keys n) n} (hk : KeySpec G r keys)
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (u v : Fin n)
    (hd : keys[u.val].depth.val = keys[v.val].depth.val)
    (hs : keys[u.val].size.val = keys[v.val].size.val)
    (ha : keys[u.val].anchor.val = keys[v.val].anchor.val) :
    predecessors G r u = predecessors G r v := by
  have hlevel : G.dist r u = G.dist r v := (hk.depth u).symm.trans (hd.trans (hk.depth v))
  have hcard : (predecessors G r u).ncard = (predecessors G r v).ncard :=
    (hk.size u).symm.trans (hs.trans (hk.size v))
  by_cases hp : 0 < G.dist r u
  · obtain ⟨x,hx,hxa⟩ := hk.anchor_mem u hp
    obtain ⟨y,hy,hya⟩ := hk.anchor_mem v (by omega)
    have hxy : x = y := Fin.ext (by omega)
    rcases hG.predecessors_laminar hc r u v hlevel with hdis | huv | hvu
    · exact False.elim (Set.disjoint_left.mp hdis hx (hxy ▸ hy))
    · exact Set.eq_of_subset_of_ncard_le huv hcard.ge
    · exact (Set.eq_of_subset_of_ncard_le hvu hcard.le).symm
  · have hu : r = u := (hc r u).dist_eq_zero_iff.mp (by omega)
    have hv : r = v := (hc r v).dist_eq_zero_iff.mp (by omega)
    rw [← hu,← hv]

/-- The source's three substantive levelwise-laminar order requirements. -/
structure IsLevelwiseLaminar {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n)
    (vertices : List (Fin n)) : Prop where
  permutation : vertices.Perm (List.finRange n)
  level_order : vertices.Pairwise (fun u v => G.dist r u ≤ G.dist r v)
  inclusion_order : ∀ i j : Fin vertices.length,
    G.dist r (vertices.get i) = G.dist r (vertices.get j) →
    predecessors G r (vertices.get j) ⊂ predecessors G r (vertices.get i) → i < j
  equal_contiguous : ∀ i j k : Fin vertices.length, i < j → j < k →
    G.dist r (vertices.get i) = G.dist r (vertices.get k) →
    predecessors G r (vertices.get i) = predecessors G r (vertices.get k) →
    predecessors G r (vertices.get j) = predecessors G r (vertices.get i)

/-- The actual radix order meets L1--L3 from the paper. -/
theorem order_levelwise_laminar {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {keys : Vector (Keys n) n} (hk : KeySpec G r keys)
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) :
    IsLevelwiseLaminar G r (order keys).1 := by
  have hs := order_sorted keys
  refine ⟨order_perm keys,?_,?_,?_⟩
  · exact hs.imp (fun {u v} h => by simpa only [hk.depth] using h.depth_le)
  · intro i j hd hp
    by_contra hn
    have hne : i ≠ j := by intro he; subst j; exact hp.ne rfl
    have hji : j < i := by omega
    have ho := hs.rel_get_of_lt hji
    have hkdepth : keys[((order keys).1.get j).val].depth.val =
        keys[((order keys).1.get i).val].depth.val := by simpa only [hk.depth] using hd.symm
    have hb := ho.size_le hkdepth
    rw [hk.size,hk.size] at hb
    have hlt := Set.ncard_lt_ncard hp
    omega
  · intro i j k hij hjk hlevel hequal
    let a := (order keys).1.get i
    let b := (order keys).1.get j
    let c := (order keys).1.get k
    have hab : Before keys[a.val] keys[b.val] := hs.rel_get_of_lt hij
    have hbc : Before keys[b.val] keys[c.val] := hs.rel_get_of_lt hjk
    have hda : keys[a.val].depth.val = keys[c.val].depth.val := by
      simpa only [hk.depth] using hlevel
    have hsa : keys[a.val].size.val = keys[c.val].size.val := by
      rw [hk.size,hk.size]
      exact congrArg Set.ncard hequal
    have haa : keys[a.val].anchor.val = keys[c.val].anchor.val :=
      congrArg Fin.val (hk.anchor_congr a c hequal)
    have habd := hab.depth_le
    have hbcd := hbc.depth_le
    have hdb : keys[b.val].depth.val = keys[a.val].depth.val := by omega
    have habs := hab.size_le hdb.symm
    have hbcs := hbc.size_le (hdb.trans hda)
    have hsb : keys[b.val].size.val = keys[a.val].size.val := by omega
    have haba := hab.anchor_le hdb.symm hsb.symm
    have hbca := hbc.anchor_le (hdb.trans hda) (hsb.trans hsa)
    have hab' : keys[b.val].anchor.val = keys[a.val].anchor.val := by omega
    exact hk.predecessors_eq hG hc b a hdb hsb hab'

structure RowSignature (n : ℕ) where
  size : ℕ
  anchor : Fin (n+1)
  accesses : ℕ

/-- Compute degree and a canonical minimum-label anchor in one incidence scan. -/
def signature {n : ℕ} : List (Fin n) → RowSignature n
  | [] => ⟨0,Fin.last n,0⟩
  | x :: xs =>
      let q := signature xs
      ⟨q.size+1,min x.castSucc q.anchor,q.accesses+3⟩

@[simp] lemma signature_size {n : ℕ} (row : List (Fin n)) :
    (signature row).size = row.length := by
  induction row <;> simp [signature, *]

@[simp] lemma signature_accesses {n : ℕ} (row : List (Fin n)) :
    (signature row).accesses = 3*row.length := by
  induction row <;> simp [signature, *] <;> omega

lemma signature_anchor_le {n : ℕ} (row : List (Fin n)) :
    ∀ x ∈ row, (signature row).anchor.val ≤ x.val := by
  induction row with
  | nil => simp
  | cons a row ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (min_le_left x.castSucc (signature row).anchor)
    · have hmin : (min a.castSucc (signature row).anchor).val ≤ (signature row).anchor.val :=
        min_le_right a.castSucc (signature row).anchor
      exact hmin.trans (ih x hx)

lemma signature_anchor_mem {n : ℕ} (row : List (Fin n)) (hne : row ≠ []) :
    ∃ x ∈ row, x.val = (signature row).anchor.val := by
  induction row with
  | nil => contradiction
  | cons a row ih =>
    by_cases hrow : row = []
    · subst row
      refine ⟨a,List.mem_cons_self,?_⟩
      simp [signature,min_eq_left (show a.castSucc ≤ Fin.last n from Nat.le_of_lt a.isLt)]
    · obtain ⟨x,hx,hxa⟩ := ih hrow
      by_cases ha : a.castSucc ≤ (signature row).anchor
      · exact ⟨a,List.mem_cons_self,by simp [signature,min_eq_left ha]⟩
      · exact ⟨x,List.mem_cons_of_mem _ hx,by simp [signature,min_eq_right (le_of_not_ge ha),hxa]⟩

lemma signature_anchor_congr {n : ℕ} (a b : List (Fin n))
    (h : ∀ x, x ∈ a ↔ x ∈ b) : (signature a).anchor = (signature b).anchor := by
  by_cases ha : a = []
  · subst a
    have hb : b = [] := List.eq_nil_iff_forall_not_mem.mpr (by intro x hx; simpa using (h x).mpr hx)
    subst b; rfl
  · have hb : b ≠ [] := by
      intro he
      obtain ⟨x,hx,hxa⟩ := signature_anchor_mem a ha
      simpa [he] using (h x).mp hx
    obtain ⟨x,hx,hxa⟩ := signature_anchor_mem a ha
    obtain ⟨y,hy,hya⟩ := signature_anchor_mem b hb
    have hxle := signature_anchor_le b x ((h x).mp hx)
    have hyle := signature_anchor_le a y ((h y).mpr hy)
    apply Fin.ext
    omega

/-- Compute the finite radix record for one input vertex. -/
def makeKey {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (v : Fin n) : Keys n × ℕ :=
  let q := signature rows[v.val]
  let sz : Fin (n+1) := ⟨q.size,by
    rw [signature_size]
    have hh := (hn v).length_le_card
    simp only [Fintype.card_fin] at hh
    omega⟩
  (⟨depths[v.val],sz,q.anchor⟩,q.accesses+2)

/-- Scan the vertices once to construct their radix records. -/
def buildKeysFrom {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) : List (Fin n) → List (Keys n) × ℕ
  | [] => ([],0)
  | v :: vs =>
      let k := makeKey depths rows hn v
      let q := buildKeysFrom depths rows hn vs
      (k.1 :: q.1,k.2+q.2+2)

lemma buildKeysFrom_values {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (vs : List (Fin n)) :
    (buildKeysFrom depths rows hn vs).1 = vs.map (fun v => (makeKey depths rows hn v).1) := by
  induction vs <;> simp [buildKeysFrom, *]

lemma buildKeysFrom_accesses {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (vs : List (Fin n)) :
    (buildKeysFrom depths rows hn vs).2 =
      3*(LinearBuckets.Adjacency.entriesFrom vs rows).1.length+4*vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [buildKeysFrom,makeKey,signature_accesses,ih,LinearBuckets.Adjacency.entriesFrom,
      List.length_cons,List.length_append,List.length_map]
    omega

structure BuiltKeys (n : ℕ) where
  keys : Vector (Keys n) n
  accesses : ℕ

def buildKeys {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) : BuiltKeys n :=
  let q := buildKeysFrom depths rows hn (List.finRange n)
  ⟨⟨q.1.toArray,by simp [q,buildKeysFrom_values]⟩,q.2+2*n⟩

@[simp] lemma buildKeys_get {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (v : Fin n) :
    (buildKeys depths rows hn).keys[v.val] = (makeKey depths rows hn v).1 := by
  simp [buildKeys,buildKeysFrom_values]

lemma buildKeys_accesses {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) :
    (buildKeys depths rows hn).accesses = 3*LinearBuckets.Adjacency.incidenceCount rows+6*n := by
  simp only [buildKeys,buildKeysFrom_accesses,List.length_finRange]
  unfold LinearBuckets.Adjacency.incidenceCount
  omega

/-- The actual key-construction scan establishes every semantic field consumed
by the L1--L3 proof; keys are not supplied as a graph-class certificate. -/
theorem buildKeys_spec {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected) (r : Fin n)
    (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup)
    (hd : ∀ v, depths[v.val].val = G.dist r v)
    (hr : ∀ v x, x ∈ rows[v.val] ↔ x ∈ predecessors G r v) :
    KeySpec G r (buildKeys depths rows hn).keys := by
  constructor
  · intro v
    simp only [buildKeys_get,makeKey]
    exact hd v
  · intro v
    simp only [buildKeys_get,makeKey,signature_size]
    have he : ((rows[v.val]).toFinset : Set (Fin n)) = predecessors G r v := by
      ext x
      simp only [Finset.mem_coe,List.mem_toFinset]
      exact hr v x
    rw [← he,Set.ncard_coe_finset,List.toFinset_card_of_nodup (hn v)]
  · intro v hv
    obtain ⟨x,hx⟩ := predecessors_nonempty (hc r v) hv
    have hne : rows[v.val] ≠ [] := by intro he; simpa [he] using (hr v x).mpr hx
    obtain ⟨y,hy,hya⟩ := signature_anchor_mem rows[v.val] hne
    refine ⟨y,(hr v y).mp hy,?_⟩
    simpa only [buildKeys_get,makeKey] using hya
  · intro u v huv
    simp only [buildKeys_get,makeKey]
    apply signature_anchor_congr
    intro x
    rw [hr u x,hr v x,huv]

/-- Input depth/predecessor arrays are transformed by verified linear scans and
three actual bucket passes into an order satisfying all of L1, L2 and L3. -/
theorem computed_order_spec {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : Fin n)
    (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup)
    (hd : ∀ v, depths[v.val].val = G.dist r v)
    (hr : ∀ v x, x ∈ rows[v.val] ↔ x ∈ predecessors G r v) :
    IsLevelwiseLaminar G r (order (buildKeys depths rows hn).keys).1 ∧
      (buildKeys depths rows hn).accesses+(order (buildKeys depths rows hn).keys).2 =
        3*LinearBuckets.Adjacency.incidenceCount rows+40*n+12 := by
  refine ⟨order_levelwise_laminar (buildKeys_spec hc r depths rows hn hd hr) hG hc,?_⟩
  rw [buildKeys_accesses,order_accesses]
  omega

end HiddenCircuits.DH.LevelOrdering
