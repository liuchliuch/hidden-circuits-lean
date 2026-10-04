import HiddenCircuits.DH.ComponentForestIndex
import HiddenCircuits.DH.ComponentForestProperties

/-! Actual equal-depth adjacency filtering and a second ordinary-input BFS
forest, for the static same-layer components used by the DH schedule. -/
namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph BreadthFirst

structure FilterRow (n : ℕ) where
  vertices : List (Fin n)
  accesses : ℕ
  allocations : ℕ

def filterDepth {n : ℕ} (d : Vector (Fin (n+1)) n) (level : Fin (n+1)) : List (Fin n) → FilterRow n
  | [] => ⟨[],0,0⟩
  | v::vs =>
      let q := filterDepth d level vs
      if d[v.val]=level then ⟨v::q.vertices,q.accesses+4,q.allocations+1⟩
      else ⟨q.vertices,q.accesses+3,q.allocations⟩

lemma filterDepth_values {n : ℕ} (d : Vector (Fin (n+1)) n) (level : Fin (n+1)) (vs : List (Fin n)) :
    (filterDepth d level vs).vertices=vs.filter (fun v => decide (d[v.val]=level)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => by_cases h : d[v.val]=level <;> simp [filterDepth,ih,h]
lemma filterDepth_resources {n : ℕ} (d : Vector (Fin (n+1)) n) (level : Fin (n+1)) (vs : List (Fin n)) :
    (filterDepth d level vs).accesses≤4*vs.length ∧ (filterDepth d level vs).allocations≤vs.length := by
  induction vs with
  | nil => simp [filterDepth]
  | cons v vs ih => simp only [filterDepth]; split <;> simp only [List.length_cons] <;> constructor <;> omega

structure FilterRows (n : ℕ) where
  rows : List (List (Fin n))
  accesses : ℕ
  allocations : ℕ

def filterFrom {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) : List (Fin n) → FilterRows n
  | [] => ⟨[],0,0⟩
  | v::vs =>
      let r := filterDepth d d[v.val] rows[v.val]
      let q := filterFrom d rows vs
      ⟨r.vertices::q.rows,r.accesses+q.accesses+3,r.allocations+q.allocations+1⟩

lemma filterFrom_values {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) (vs : List (Fin n)) :
    (filterFrom d rows vs).rows=vs.map (fun v => (rows[v.val]).filter (fun u => decide (d[u.val]=d[v.val]))) := by
  induction vs <;> simp [filterFrom,filterDepth_values, *]
lemma filterFrom_resources {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) (vs : List (Fin n)) :
    (filterFrom d rows vs).accesses≤4*(neighborsFrom rows vs).1.length+3*vs.length ∧
      (filterFrom d rows vs).allocations≤(neighborsFrom rows vs).1.length+vs.length := by
  induction vs with
  | nil => simp [filterFrom,neighborsFrom]
  | cons v vs ih =>
    have h := filterDepth_resources d d[v.val] rows[v.val]
    simp only [filterFrom,neighborsFrom,List.length_append,List.length_cons]
    constructor <;> omega

structure Filtered (n : ℕ) where
  rows : Vector (List (Fin n)) n
  accesses : ℕ
  allocations : ℕ

def sameDepthRows {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) : Filtered n :=
  let q := filterFrom d rows (List.finRange n)
  ⟨⟨q.rows.toArray,by simp [q,filterFrom_values]⟩,q.accesses+2*n,q.allocations+n⟩

lemma sameDepthRows_get {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) (v : Fin n) :
    (sameDepthRows d rows).rows[v.val] = (rows[v.val]).filter (fun u => decide (d[u.val]=d[v.val])) := by
  simp [sameDepthRows,filterFrom_values]

lemma sameDepthRows_resources {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) :
    (sameDepthRows d rows).accesses≤4*LinearBuckets.Adjacency.incidenceCount rows+5*n ∧
      (sameDepthRows d rows).allocations≤LinearBuckets.Adjacency.incidenceCount rows+2*n := by
  have h := filterFrom_resources d rows (List.finRange n)
  rw [neighbors_all_length,List.length_finRange] at h
  simp only [sameDepthRows]
  constructor <;> omega

lemma sameDepthRows_incidence {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) :
    LinearBuckets.Adjacency.incidenceCount (sameDepthRows d rows).rows≤LinearBuckets.Adjacency.incidenceCount rows := by
  rw [←sum_row_lengths,←sum_row_lengths]
  apply Finset.sum_le_sum
  intro v hv
  rw [sameDepthRows_get]
  exact List.length_filter_le _ _

lemma sameDepthRows_nodup {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀v : Fin n, (rows[v.val]).Nodup) : ∀v : Fin n, ((sameDepthRows d rows).rows[v.val]).Nodup := by
  intro v;rw [sameDepthRows_get];exact (hn v).filter _

def sameDepthGraph {n : ℕ} (G : SimpleGraph (Fin n)) (d : Vector (Fin (n+1)) n) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ d[u.val]=d[v.val]
  symm := by intro u v h;exact ⟨h.1.symm,h.2.symm⟩
  loopless := ⟨by intro v h;exact G.loopless.irrefl v h.1⟩

instance sameDepthGraph_decidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : Vector (Fin (n+1)) n) : DecidableRel (sameDepthGraph G d).Adj := by
  intro u v;change Decidable (G.Adj u v ∧ d[u.val]=d[v.val]);infer_instance

lemma sameDepthRows_represents {n : ℕ} (G : SimpleGraph (Fin n)) (d : Vector (Fin (n+1)) n)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows) :
    LinearBuckets.Adjacency.Represents (sameDepthGraph G d) (sameDepthRows d rows).rows := by
  intro u v
  rw [sameDepthRows_get]
  simp only [List.mem_filter,decide_eq_true_eq]
  rw [hr u v]
  change (G.Adj u v ∧ d[v.val]=d[u.val]) ↔ (G.Adj u v ∧ d[u.val]=d[v.val])
  exact and_congr_right (fun _ => eq_comm)

/-- Filtering is followed by the same verified ordinary BFS forest and direct
root indexing pass; no layer-component certificate is supplied. -/
def sameDepthForest {n : ℕ} (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) : IndexedOutput n :=
  let f := sameDepthRows d rows
  let q := indexed f.rows
  {q with accesses:=f.accesses+q.accesses, allocations:=f.allocations+q.allocations}

theorem sameDepthForest_components {n : ℕ} (G : SimpleGraph (Fin n))
    (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows) :
    (sameDepthForest d rows).roots.Nodup ∧
    (∀u v, (sameDepthForest d rows).owners[u.val]=(sameDepthForest d rows).owners[v.val] ↔
      (sameDepthGraph G d).Reachable u v) ∧
    (∀r∈(sameDepthForest d rows).roots, ((sameDepthForest d rows).buckets[r.val]).Nodup ∧
      ∀v, v∈(sameDepthForest d rows).buckets[r.val] ↔ (sameDepthGraph G d).Reachable r v) ∧
    (∀r, r∉(sameDepthForest d rows).roots → (sameDepthForest d rows).buckets[r.val]=[]) ∧
    (∀v : Fin n, (sameDepthForest d rows).owners[v.val]∈(sameDepthForest d rows).roots ∧
      v∈(sameDepthForest d rows).buckets[((sameDepthForest d rows).owners[v.val]).val]) := by
  have hf := sameDepthRows_represents G d rows hr
  exact ⟨indexed_roots_nodup _ hf,forest_owner_iff _ hf,indexed_bucket _ hf,indexed_bucket_empty _,indexed_owner_bucket _ hf⟩

lemma sameDepthGraph_adj {n : ℕ} (G : SimpleGraph (Fin n)) (d : Vector (Fin (n+1)) n) (u v : Fin n) :
    (sameDepthGraph G d).Adj u v ↔ G.Adj u v ∧ d[u.val].val=d[v.val].val := by
  simp [sameDepthGraph,Fin.ext_iff]

theorem sameDepthForest_resources {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (hn : ∀v : Fin n, (rows[v.val]).Nodup) :
    (sameDepthForest d rows).accesses≤22*G.edgeFinset.card+27*n+7 ∧
      (sameDepthForest d rows).allocations≤22*G.edgeFinset.card+27*n+7 := by
  have hf := sameDepthRows_represents G d rows hr
  have hn' := sameDepthRows_nodup d rows hn
  have hi := indexed_resources (sameDepthGraph G d) (sameDepthRows d rows).rows hf hn'
  have hb := sameDepthRows_resources d rows
  have hle : sameDepthGraph G d≤G := fun _ _ h => h.1
  have he := Finset.card_le_card (SimpleGraph.edgeFinset_mono hle)
  rw [LinearBuckets.Adjacency.incidenceCount_eq_degree_sum G rows hr hn,G.sum_degrees_eq_twice_card_edges] at hb
  simp only [sameDepthForest]
  constructor <;> omega

end HiddenCircuits.DH.ComponentForest
