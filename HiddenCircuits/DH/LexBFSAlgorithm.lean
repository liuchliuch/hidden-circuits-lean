import HiddenCircuits.DH.LexBFSSweep
import HiddenCircuits.DH.LexBFSOutput

/-! Ordinary adjacency-list, arbitrary-tie-order wrapper for the verified pointer sweeps.
All preprocessing, capacity computation, array initialization and output relabeling is counted. -/
namespace HiddenCircuits.DH.LexBFSAlgorithm
open LexBFSPartition
open LinearBuckets

/-- Map rank-coordinate events back with direct forward-array reads. -/
def restore {n : ℕ} (tau : Vector (Fin n) n) :
    List (LexBFSModel.Event (Fin n)) → Counted (List (LexBFSModel.Event (Fin n)))
  | [] => ⟨[],0⟩
  | e::es =>
      let q := restore tau es
      ⟨⟨tau[e.vertex.val],e.sliceSize⟩::q.value,q.accesses+4⟩

@[simp] lemma restore_value {n : ℕ} (tau : Vector (Fin n) n) (es : List (LexBFSModel.Event (Fin n))) :
    (restore tau es).value = es.map (LexBFSModel.Event.map (fun v => tau[v.val])) := by
  induction es <;> simp [restore,LexBFSModel.Event.map, *]

@[simp] lemma restore_accesses {n : ℕ} (tau : Vector (Fin n) n) (es : List (LexBFSModel.Event (Fin n))) :
    (restore tau es).accesses = 4*es.length := by
  induction es <;> simp [restore, *] <;> omega

/-- Empty graphs return before any cell-array allocation. Both flags read only original rows. -/
def runOrdered {n : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) : Counted (List (LexBFSModel.Event (Fin n))) :=
  if n=0 then ⟨[],0⟩ else
    let o := LexBFSInput.ofList tie hp
    let normal := LexBFSInput.normalize o.order rows
    let raw := LexBFSPartition.sweep normal.rows first
    let out := restore o.order.vertexAt raw.events
    ⟨out.value,o.accesses+normal.accesses+raw.accesses+out.accesses⟩

/-- The executable ordinary-input result is exactly stable LexBFS on G, or its complement
preference when first=false, in the supplied tie order. -/
theorem runOrdered_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (runOrdered rows first tie hp).value =
      LexBFSModel.sweep (fun u v => decide (G.Adj u v)) first tie := by
  by_cases hz : n=0
  · have hlen : tie.length=0 := by simpa [hz] using hp.length_eq
    have ht := List.length_eq_zero_iff.mp hlen
    simp [runOrdered,hz,ht,LexBFSModel.sweep,LexBFSModel.run]
  · let o := (LexBFSInput.ofList tie hp).order
    let normal := LexBFSInput.normalize o rows
    have hs := LexBFSInput.normalize_spec o G rows hr hn
    have hraw := LexBFSPartition.sweep_refines normal.rows first (fun i => (hs.2.1 i).2)
    have hadj : (fun u v : Fin n => decide (v ∈ normal.rows[u.val])) =
        (fun u v => decide (G.Adj (o.equiv u) (o.equiv v))) := by
      funext u v
      exact decide_eq_decide.mpr (hs.1 u v)
    have hrestore := LexBFSInput.sweep_in_rank_coordinates o (fun u v => decide (G.Adj u v)) first
    have htau : o.vertexAt.toList=tie := LexBFSInput.ofList_vertexAt tie hp
    rw [htau] at hrestore
    simp only [runOrdered,hz,↓reduceIte]
    change (restore o.vertexAt (LexBFSPartition.sweep normal.rows first).events).value = _
    rw [restore_value,hraw,hadj]
    exact hrestore.symm

/-- Includes input relabeling, sorting, inverse arrays, capacity scan, heap initialization,
sparse sweep, and output remapping; there is no supplied certificate. -/
theorem runOrdered_accesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (runOrdered rows first tie hp).accesses ≤ 66*(n+Adjacency.incidenceCount rows) := by
  by_cases hz : n=0
  · simp [runOrdered,hz]
  · let o := (LexBFSInput.ofList tie hp).order
    let normal := LexBFSInput.normalize o rows
    have hs := LexBFSInput.normalize_spec o G rows hr hn
    have hm := LexBFSInput.normalize_incidence o G rows hr hn
    have hraw := LexBFSPartition.sweep_refines normal.rows first (fun i => (hs.2.1 i).2)
    have hc := LexBFSPartition.sweep_accesses normal.rows first (fun i => (hs.2.1 i).2)
    have hlen : (LexBFSPartition.sweep normal.rows first).events.length=n := by
      have hp' := LexBFSModel.sweep_perm (fun u v => decide (v ∈ normal.rows[u.val])) first (List.finRange n)
      rw [← hraw] at hp'
      simpa using hp'.length_eq
    have ho := LexBFSInput.ofList_accesses tie hp
    have hncount := hs.2.2
    have hout := restore_accesses o.vertexAt (LexBFSPartition.sweep normal.rows first).events
    rw [hlen] at hout
    change Adjacency.incidenceCount normal.rows = Adjacency.incidenceCount rows at hm
    simp only [runOrdered,hz,↓reduceIte]
    change (LexBFSInput.ofList tie hp).accesses+normal.accesses+
      (LexBFSPartition.sweep normal.rows first).accesses+
      (restore o.vertexAt (LexBFSPartition.sweep normal.rows first).events).accesses ≤ _
    change normal.accesses = _ at hncount
    omega

theorem runOrdered_perm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    ((runOrdered rows first tie hp).value.map LexBFSModel.Event.vertex).Perm (List.finRange n) := by
  rw [runOrdered_correct G rows hr hn first tie hp]
  exact (LexBFSModel.sweep_perm _ _ _).trans hp

/-- Literal three-array output, including inverse ranks and all constant-time slice intervals. -/
def compact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) : Counted (CompactOutput n) :=
  let r := runOrdered rows first tie hp
  let out := materialize r.value (runOrdered_perm G rows hr hn first tie hp)
  ⟨out.value,r.accesses+out.accesses⟩

theorem compact_accesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (compact G rows hr hn first tie hp).accesses ≤ 75*(n+Adjacency.incidenceCount rows) := by
  have h := runOrdered_accesses G rows hr hn first tie hp
  simp only [compact,materialize_accesses]
  omega

/-- The complete compact frontend has a literal graph-size linear access bound. -/
theorem compact_graph_accesses {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (compact G rows hr hn first tie hp).accesses ≤ 150*(n+G.edgeFinset.card) := by
  have h := compact_accesses G rows hr hn first tie hp
  rw [Adjacency.incidenceCount_eq_degree_sum G rows hr hn,G.sum_degrees_eq_twice_card_edges] at h
  omega

theorem runOrdered_slices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    LexBFSModel.SliceCorrect (LexBFSModel.prefers (fun u v => decide (G.Adj u v)) first) []
      (runOrdered rows first tie hp).value := by
  rw [runOrdered_correct G rows hr hn first tie hp]
  exact LexBFSModel.sweep_slices _ _ _

theorem compact_vertices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) :
    (compact G rows hr hn first tie hp).value.order.vertexAt.toList =
      (LexBFSModel.sweep (fun u v => decide (G.Adj u v)) first tie).map LexBFSModel.Event.vertex := by
  simp only [compact,materialize_vertices,runOrdered_correct G rows hr hn first tie hp]

/-- Actual output arrays expose the same bounded equal-profile slice intervals as the
mathematical sweep, using exactly one stored length read for each interval query. -/
theorem compact_slice_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (first : Bool)
    (tie : List (Fin n)) (hp : tie.Perm (List.finRange n)) (i : Fin n) :
    let es := (runOrdered rows first tie hp).value
    let o := (compact G rows hr hn first tie hp).value
    let range := (o.slice i).value
    range.1=i.val ∧ range.1 < range.2 ∧ range.2 ≤ n ∧
      ∀ v, v ∈ (o.order.vertexAt.toList.drop range.1).take (range.2-range.1) ↔
        v ∈ o.order.vertexAt.toList.drop i.val ∧
          LexBFSModel.SameProfile (LexBFSModel.prefers (fun u v => decide (G.Adj u v)) first)
            ((es.take i.val).map LexBFSModel.Event.vertex)
            (es[i.val]'(by
              have hlen : es.length=n := by
                simpa [es] using (runOrdered_perm G rows hr hn first tie hp).length_eq
              omega)).vertex v :=
  materialize_slice_correct _ (runOrdered_perm G rows hr hn first tie hp) _
    (runOrdered_slices G rows hr hn first tie hp) i

end HiddenCircuits.DH.LexBFSAlgorithm
