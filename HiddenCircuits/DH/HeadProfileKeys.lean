import HiddenCircuits.DH.HeadProfileDegrees
import HiddenCircuits.DH.ProfileCardinality

/-! Actual bounded size keys for the global stable profile-head sorting pass.
Complement keys use only original-graph common counts and original degrees. -/
namespace HiddenCircuits.DH.HeadProfileCounts
open scoped BigOperators
open LinearBuckets

/-- Truncated subtraction is performed only after adding the common-neighbor term. -/
def keyNat {n : ℕ} (normal : Bool) (common degree : Vector ℕ n) (parent head : Fin n) : ℕ :=
  if normal then common[head.val] else n+common[head.val]-degree[parent.val]-degree[head.val]

/-- Clipping totalizes the runtime on arbitrary arrays. Semantic correctness proves
it is inactive on every actual supplied parent/head incidence. -/
def keyValue {n : ℕ} (normal : Bool) (common degree : Vector ℕ n) (parent head : Fin n) : Fin (n+1) :=
  ⟨min (keyNat normal common degree parent head) n,by omega⟩

/-- Three reads, one key write and one input-list step suffice per incidence. -/
def writeKeys {n : ℕ} (normal : Bool) (common degree : Vector ℕ n) :
    List (Fin n × Fin n) → Vector (Fin (n+1)) n → Vector (Fin (n+1)) n × ℕ
  | [],keys => (keys,0)
  | e::es,keys =>
      let q := writeKeys normal common degree es (keys.set e.2.val (keyValue normal common degree e.1 e.2))
      (q.1,q.2+5)

@[simp] lemma writeKeys_accesses {n : ℕ} (normal : Bool) (common degree : Vector ℕ n)
    (heads : List (Fin n × Fin n)) (keys : Vector (Fin (n+1)) n) :
    (writeKeys normal common degree heads keys).2 = 5*heads.length := by
  induction heads generalizing keys <;> simp [writeKeys, *] <;> omega

lemma writeKeys_absent {n : ℕ} (normal : Bool) (common degree : Vector ℕ n)
    (heads : List (Fin n × Fin n)) (keys : Vector (Fin (n+1)) n)
    (head : Fin n) (hh : head∉heads.map Prod.snd) :
    (writeKeys normal common degree heads keys).1[head.val] = keys[head.val] := by
  induction heads generalizing keys with
  | nil => rfl
  | cons e es ih =>
    have hne : e.2.val≠head.val := by
      intro he
      exact hh (List.mem_map.mpr ⟨e,List.mem_cons_self,Fin.ext he⟩)
    have ht : head∉es.map Prod.snd := fun hm=>hh (List.mem_cons_of_mem _ hm)
    rw [writeKeys,ih _ ht]
    simp [hne]

lemma writeKeys_get {n : ℕ} (normal : Bool) (common degree : Vector ℕ n)
    (heads : List (Fin n × Fin n)) (keys : Vector (Fin (n+1)) n)
    (hn : (heads.map Prod.snd).Nodup) (parent head : Fin n) (hm : (parent,head)∈heads) :
    (writeKeys normal common degree heads keys).1[head.val] = keyValue normal common degree parent head := by
  induction heads generalizing keys with
  | nil => simp at hm
  | cons e es ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | hm
    · subst e
      rw [writeKeys,writeKeys_absent _ _ _ _ _ _ hnd.1]
      simp
    · exact ih _ hnd.2 hm

structure KeyResult (n : ℕ) where
  keys : Vector (Fin (n+1)) n
  accesses : ℕ

/-- Ordinary rows are the sole graph input; neither complement edges nor profile sets
are enumerated by this code. -/
def profileKeys {n : ℕ} (rows : Vector (List (Fin n)) n) (heads : List (Fin n × Fin n))
    (normal : Bool) : KeyResult n :=
  let d := profileData rows heads
  let k := writeKeys normal d.common d.degree heads (Vector.replicate n 0)
  ⟨k.1,d.accesses+k.2+n⟩

theorem profileKeys_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup) (normal : Bool) :
    (profileKeys rows heads normal).accesses ≤
      30*(∑ i : Fin n,rows[i.val].length)+13*n+7*heads.length := by
  have hd := profileData_accesses rows heads hn
  simp only [profileKeys,writeKeys_accesses]
  omega

lemma commonCounts_profile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hrows : ∀ i : Fin n,(rows[i.val]).Nodup)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup)
    (parent head : Fin n) (hm : (parent,head)∈heads) :
    (commonCounts rows heads).counts[head.val] = (pivotProfile G parent head).ncard := by
  rw [commonCounts_get G rows hr hrows heads hn parent head hm]
  have he : pivotProfile G parent head =
      (↑(G.neighborFinset parent ∩ G.neighborFinset head) : Set (Fin n)) := by
    ext z
    simp [pivotProfile]
  rw [he]
  exact (Set.ncard_coe_finset _).symm

lemma degreeCounts_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ i : Fin n,(rows[i.val]).Nodup) (i : Fin n) :
    (degreeCounts rows).counts[i.val] = (G.neighborSet i).ncard := by
  rw [degreeCounts_get G rows hr hn]
  have he : (↑(G.neighborFinset i) : Set (Fin n)) = G.neighborSet i := by ext j; simp
  change (G.neighborFinset i).card = (G.neighborSet i).ncard
  rw [←he]
  exact (Set.ncard_coe_finset _).symm

lemma profileKeys_value {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup)
    (normal : Bool) (parent head : Fin n) (hm : (parent,head)∈heads) :
    (profileKeys rows heads normal).keys[head.val] =
      keyValue normal (commonCounts rows heads).counts (degreeCounts rows).counts parent head := by
  exact writeKeys_get normal _ _ heads _ hn parent head hm

/-- The normal-sweep sorting key is the literal finite pivot-profile cardinality. -/
theorem profileKeys_normal_get {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hrows : ∀ i : Fin n,(rows[i.val]).Nodup)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup)
    (parent head : Fin n) (hm : (parent,head)∈heads) :
    ((profileKeys rows heads true).keys[head.val]).val = (pivotProfile G parent head).ncard := by
  have hb : (pivotProfile G parent head).ncard≤n := by simpa using Set.ncard_le_card (pivotProfile G parent head)
  rw [profileKeys_value rows heads hn true parent head hm]
  change min ((commonCounts rows heads).counts[head.val]) n = _
  rw [commonCounts_profile G rows hr hrows heads hn parent head hm,Nat.min_eq_left hb]

/-- For complementary nonpreferred children the original parent/head pair is adjacent.
The actual three-read arithmetic key equals its complement-profile size exactly. -/
theorem profileKeys_complement_get {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hrows : ∀ i : Fin n,(rows[i.val]).Nodup)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup)
    (parent head : Fin n) (hm : (parent,head)∈heads) (hadj : G.Adj parent head) :
    ((profileKeys rows heads false).keys[head.val]).val = (pivotProfile Gᶜ parent head).ncard := by
  have hb : (pivotProfile Gᶜ parent head).ncard≤n := by simpa using Set.ncard_le_card (pivotProfile Gᶜ parent head)
  have he : n+(pivotProfile G parent head).ncard-(G.neighborSet parent).ncard-(G.neighborSet head).ncard =
      (pivotProfile Gᶜ parent head).ncard := by
    simpa using (complement_pivotProfile_ncard hadj).symm
  rw [profileKeys_value rows heads hn false parent head hm]
  change min (n+(commonCounts rows heads).counts[head.val]-(degreeCounts rows).counts[parent.val]-
    (degreeCounts rows).counts[head.val]) n = _
  rw [commonCounts_profile G rows hr hrows heads hn parent head hm,
    degreeCounts_neighbor G rows hr hrows parent,degreeCounts_neighbor G rows hr hrows head,
    he,Nat.min_eq_left hb]

end HiddenCircuits.DH.HeadProfileCounts
