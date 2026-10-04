import HiddenCircuits.DH.CographFrontend
import HiddenCircuits.DH.ComponentForestSameDepth
import HiddenCircuits.DH.ComponentForestProperties
import HiddenCircuits.DH.HeadProfileDegrees

/-! Ordinary sparse graph input is transformed once into the static BFS schedule.
The schedule contains only computed arrays and lists; no module or pruning
certificate is supplied to this construction. -/
namespace HiddenCircuits.DH.LayerInput
open SimpleGraph LexBFSPartition LinearBuckets

/-- Stable direct-address depth buckets. Reversing before cons insertion retains
the supplied order inside every depth bucket. -/
def bucketBy {n : ℕ} (depths : Vector (Fin (n+1)) n) (vs : List (Fin n)) :
    Counted (Vector (List (Fin n)) (n+1)) :=
  let q := fill (fun v => depths[v.val]) vs.reverse (Vector.replicate (n+1) [])
  ⟨q.1,q.2+2*vs.length+(n+1)⟩

lemma bucketBy_get {n : ℕ} (depths : Vector (Fin (n+1)) n) (vs : List (Fin n)) (k : Fin (n+1)) :
    (bucketBy depths vs).value[k.val] = vs.filter (fun v => depths[v.val] == k) := by
  simp [bucketBy,fill_get,List.filter_reverse]

lemma bucketBy_accesses {n : ℕ} (depths : Vector (Fin (n+1)) n) (vs : List (Fin n)) :
    (bucketBy depths vs).accesses=5*vs.length+n+1 := by
  simp [bucketBy];omega

structure Prepared (n : ℕ) where
  owners : Vector (Fin n) n
  depths : Vector (Fin (n+1)) n
  previous : Vector (List (Fin n)) n
  degree : Vector ℕ n
  componentOwner : Vector (Fin n) n
  components : Vector (List (Fin n)) n
  componentByLevel : Vector (List (Fin n)) (n+1)
  vertexByLevel : Vector (List (Fin n)) (n+1)
  previous_nodup : ∀v : Fin n, previous[v.val].Nodup
  component_nodup : ∀v : Fin n, components[v.val].Nodup
  accesses : ℕ

/-- A bounded-key sort orders all vertices by their original predecessor count.
No current neighborhoods are recomputed or compared by the sorting algorithm. -/
def byPreviousSize {n : ℕ} (keys : Vector (LevelOrdering.Keys n) n) : Counted (List (Fin n)) :=
  let q := sort (fun v : Fin n => keys[v.val].size.rev) (List.finRange n)
  ⟨q.1,q.2+2*n⟩

lemma byPreviousSize_perm {n : ℕ} (keys : Vector (LevelOrdering.Keys n) n) :
    (byPreviousSize keys).value.Perm (List.finRange n) := sort_perm _ _

lemma byPreviousSize_sorted {n : ℕ} (keys : Vector (LevelOrdering.Keys n) n) :
    (byPreviousSize keys).value.Pairwise (fun u v => keys[u.val].size.val≤keys[v.val].size.val) := by
  have h := sort_descending (fun v : Fin n => keys[v.val].size.rev) (List.finRange n)
  apply h.imp
  intro u v huv
  simpa only [Fin.rev_le_rev] using huv

lemma byPreviousSize_accesses {n : ℕ} (keys : Vector (LevelOrdering.Keys n) n) :
    (byPreviousSize keys).accesses=11*n+4 := by
  simp only [byPreviousSize,sort_accesses,List.length_finRange];omega

/-- One BFS forest, one equal-depth component forest, predecessor filtering,
original degree scan, size-key scan and stable bucket passes. -/
def prepare {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) : Prepared n :=
  let bfs := ComponentForest.build rows
  let comps := ComponentForest.sameDepthForest bfs.depths rows
  let prev := BreadthFirst.previous bfs.depths rows
  let keys := LevelOrdering.buildKeys bfs.depths prev.rows (BreadthFirst.previous_nodup _ _ hn)
  let degree := HeadProfileCounts.degreeCounts rows
  let ordered := byPreviousSize keys.keys
  let vertices := bucketBy bfs.depths ordered.value
  let blocks := bucketBy bfs.depths comps.roots
  { owners:=bfs.owners
    depths:=bfs.depths
    previous:=prev.rows
    degree:=degree.counts
    componentOwner:=comps.owners
    components:=comps.buckets
    componentByLevel:=blocks.value
    vertexByLevel:=vertices.value
    previous_nodup:=BreadthFirst.previous_nodup _ _ hn
    component_nodup:=by
      intro v
      by_cases hv : v∈comps.roots
      · exact ((ComponentForest.sameDepthForest_components G bfs.depths rows hr).2.2.1 v hv).1
      · rw [(ComponentForest.sameDepthForest_components G bfs.depths rows hr).2.2.2.1 v hv]
        exact List.nodup_nil
    accesses:=bfs.accesses+comps.accesses+prev.accesses+keys.accesses+degree.accesses+
      ordered.accesses+vertices.accesses+blocks.accesses }

@[simp] lemma prepare_depths {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) :
    (prepare G rows hr hn).depths=(ComponentForest.build rows).depths := rfl

@[simp] lemma prepare_previous {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (v : Fin n) :
    (prepare G rows hr hn).previous[v.val]=
      (rows[v.val]).filter (fun u => decide
        ((prepare G rows hr hn).depths[u.val].val+1=(prepare G rows hr hn).depths[v.val].val)) := by
  exact BreadthFirst.previous_get _ _ _

@[simp] lemma prepare_degree {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (v : Fin n) :
    (prepare G rows hr hn).degree[v.val]=rows[v.val].length := HeadProfileCounts.degreeCounts_value _ _

lemma prepare_vertex_bucket {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) (k : Fin (n+1)) :
    ((prepare G rows hr hn).vertexByLevel[k.val]).Nodup ∧
      (∀v, v∈(prepare G rows hr hn).vertexByLevel[k.val] ↔ (prepare G rows hr hn).depths[v.val]=k) ∧
      ((prepare G rows hr hn).vertexByLevel[k.val]).Pairwise
        (fun u v => ((prepare G rows hr hn).previous[u.val]).length≤((prepare G rows hr hn).previous[v.val]).length) := by
  let bfs := ComponentForest.build rows
  let prev := BreadthFirst.previous bfs.depths rows
  let keys := LevelOrdering.buildKeys bfs.depths prev.rows (BreadthFirst.previous_nodup _ _ hn)
  let ordered := byPreviousSize keys.keys
  change ((bucketBy bfs.depths ordered.value).value[k.val]).Nodup ∧ _
  rw [bucketBy_get]
  have hp := byPreviousSize_perm keys.keys
  refine ⟨(hp.nodup_iff.mpr (List.nodup_finRange n)).filter _,?_,?_⟩
  · intro v
    change v∈(bucketBy bfs.depths ordered.value).value[k.val] ↔ bfs.depths[v.val]=k
    rw [bucketBy_get,List.mem_filter]
    simp only [beq_iff_eq]
    exact ⟨fun h=>h.2,fun h=>⟨hp.mem_iff.mpr (List.mem_finRange v),h⟩⟩
  · have h := (byPreviousSize_sorted keys.keys).filter (fun v=>bfs.depths[v.val] == k)
    change ((bucketBy bfs.depths ordered.value).value[k.val]).Pairwise _
    rw [bucketBy_get]
    apply h.imp
    intro u v huv
    simpa only [keys,LevelOrdering.buildKeys_get,LevelOrdering.makeKey,LevelOrdering.signature_size] using huv

/-- The initial schedule is genuinely linear for disconnected ordinary input. -/
theorem prepare_accesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀v : Fin n, rows[v.val].Nodup) :
    (prepare G rows hr hn).accesses ≤ 54*G.edgeFinset.card+84*n+17 := by
  let bfs := ComponentForest.build rows
  let comps := ComponentForest.sameDepthForest bfs.depths rows
  let prev := BreadthFirst.previous bfs.depths rows
  let keys := LevelOrdering.buildKeys bfs.depths prev.rows (BreadthFirst.previous_nodup _ _ hn)
  let degree := HeadProfileCounts.degreeCounts rows
  let ordered := byPreviousSize keys.keys
  have hb := (ComponentForest.build_spec G rows hr hn).2.2.2.2.1
  have hc := (ComponentForest.sameDepthForest_resources G bfs.depths rows hr hn).1
  have hp := BreadthFirst.previous_accesses bfs.depths rows
  have hpi := BreadthFirst.previous_incidence_le bfs.depths rows
  have hk := LevelOrdering.buildKeys_accesses bfs.depths prev.rows (BreadthFirst.previous_nodup _ _ hn)
  have hd := HeadProfileCounts.degreeCounts_accesses rows
  have ho := byPreviousSize_accesses keys.keys
  have hol : ordered.value.length=n := by simpa using (byPreviousSize_perm keys.keys).length_eq
  have hv := bucketBy_accesses bfs.depths ordered.value
  have hbc := bucketBy_accesses bfs.depths comps.roots
  have hcl : comps.roots.length≤n := by
    have hh := (ComponentForest.sameDepthForest_components G bfs.depths rows hr).1.length_le_card
    simpa using hh
  have hi := Adjacency.incidenceCount_eq_degree_sum G rows hr hn
  rw [G.sum_degrees_eq_twice_card_edges] at hi
  have hir := CographFrontend.incidenceCount_eq_sum rows
  change bfs.accesses+comps.accesses+prev.accesses+keys.accesses+degree.accesses+
    ordered.accesses+(bucketBy bfs.depths ordered.value).accesses+(bucketBy bfs.depths comps.roots).accesses≤_
  change bfs.accesses≤_ at hb
  change comps.accesses≤_ at hc
  change prev.accesses≤_ at hp
  change Adjacency.incidenceCount prev.rows≤_ at hpi
  change keys.accesses=_ at hk
  change degree.accesses=_ at hd
  change ordered.accesses=_ at ho
  omega

end HiddenCircuits.DH.LayerInput
