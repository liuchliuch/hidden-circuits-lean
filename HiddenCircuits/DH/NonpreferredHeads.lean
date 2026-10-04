import HiddenCircuits.DH.SliceHeadBuckets
import HiddenCircuits.DH.BatchAdjacency

/-! Ordinary adjacency-list construction of nonpreferred slice-child heads.
One batched marker pass classifies all parent/child pairs; no matrix is built. -/
namespace HiddenCircuits.DH.NonpreferredHeads
open LexBFSModel LinearBuckets SliceHeads

/-- Consume aligned query answers, retaining precisely the nonpreferred edges. -/
def select {α : Type*} (preferred : Bool) : List α → List Bool → List α × ℕ
  | [],_ => ([],0)
  | _,[] => ([],0)
  | x::xs,b::bs =>
      let q := select preferred xs bs
      if b==preferred then (q.1,q.2+3) else (x::q.1,q.2+4)

lemma select_map {α : Type*} (s : Bool) (xs : List α) (f : α → Bool) :
    (select s xs (xs.map f)).1 = xs.filter (fun x => f x != s) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x == s <;> simp_all [select]

lemma select_bounds {α : Type*} (s : Bool) (xs : List α) (answers : List Bool) :
    (select s xs answers).1.length≤xs.length ∧ (select s xs answers).2≤4*xs.length := by
  induction xs generalizing answers with
  | nil => simp [select]
  | cons x xs ih =>
    cases answers with
    | nil => simp [select]
    | cons b bs =>
      have h := ih bs
      cases he : b==s <;> simp [select,he] <;> omega

/-- One array of parent buckets for all retained edges. -/
def group {n : ℕ} (entries : List (Fin n × Fin n)) : Children n :=
  let b := fill Prod.fst entries (Vector.replicate n [])
  let r := Adjacency.finish (List.finRange n) b.1
  ⟨⟨r.1.toArray,by simp [r]⟩,b.2+r.2+3*n⟩

lemma group_get {n : ℕ} (entries : List (Fin n × Fin n)) (i : Fin n) :
    (group entries).rows[i.val] = (entries.filter (fun p => p.1==i)).map Prod.snd := by
  simp [group,Adjacency.finish_values,fill_get]

lemma group_accesses {n : ℕ} (entries : List (Fin n × Fin n)) :
    (group entries).accesses=5*entries.length+5*n := by
  let bins := (fill Prod.fst entries (Vector.replicate n [])).1
  have hperm : (collect (List.finRange n) bins).1.Perm entries := by
    have hp : (collect (List.finRange n) bins).1.Perm (collect (List.finRange n).reverse bins).1 := by
      rw [collect_values,collect_values]
      exact (List.reverse_perm _).symm.flatMap_right _
    exact hp.trans (sort_perm Prod.fst entries)
  have he := hperm.length_eq
  simp only [group,fill_accesses,Adjacency.finish_accesses,List.length_finRange]
  change 3*entries.length+(2*(collect (List.finRange n) bins).1.length+2*n)+3*n = _
  omega

/-- Both list/vector conversions are charged in addition to the vector query
engine's own accesses. Every original incidence list is scanned once per batch. -/
def construct {n : ℕ} (rows : Vector (List (Fin n)) n) (preferred : Bool)
    (events : List (Event (Fin n))) : Children n :=
  let p := build events
  let e := parentEntries p.events
  let a := BatchAdjacency.runList rows e.1
  let f := select preferred e.1 a.1.toList
  let g := group f.1
  ⟨g.rows,p.accesses+e.2+a.2+f.2+g.accesses+2*e.1.length⟩

lemma answers_list {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (queries : List (Fin n × Fin n)) :
    (BatchAdjacency.runList rows queries).1.toList =
      queries.map (fun p => decide (G.Adj p.1 p.2)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h := BatchAdjacency.runList_graph G rows hr queries ⟨i,by simpa using hi⟩
    simpa using h

/-- Exact nonpreferred immediate-child lists, in the original sweep order. -/
theorem construct_get {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (s : Bool) (events : List (Event (Fin n))) (i : Fin n) :
    (construct rows s events).rows[i.val] =
      ((((parentEntries (build events).events).1.filter
        (fun p => decide (G.Adj p.1 p.2) != s)).filter (fun p => p.1==i)).map Prod.snd) := by
  simp only [construct,group_get,answers_list G rows hr,select_map]

/-- Costs depend on original adjacency entries, not on complement density or
repeated per-slice vertex scans. -/
theorem construct_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (s : Bool) (events : List (Event (Fin n))) :
    (construct rows s events).accesses≤
      6*(∑i:Fin n, rows[i.val].length)+34*events.length+11*n := by
  have hp := build_accesses events
  have he := parentEntries_bounds (build events).events
  have ha := BatchAdjacency.runList_accesses rows (parentEntries (build events).events).1
  have hf := select_bounds s (parentEntries (build events).events).1
    (BatchAdjacency.runList rows (parentEntries (build events).events).1).1.toList
  have hg := group_accesses (select s (parentEntries (build events).events).1
    (BatchAdjacency.runList rows (parentEntries (build events).events).1).1.toList).1
  have hlen : (build events).events.length=events.length := scan_length 0 events []
  simp only [construct]
  omega

/-- Finite ordinary-input sweeps produce the exact nonpreferred-head frontend
within a bound linear in the original graph's incidence count. -/
theorem construct_sweep_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (a : Fin n → Fin n → Bool) (s : Bool) (tie : List (Fin n))
    (htie : tie.Perm (List.finRange n)) :
    (construct rows s (sweep a s tie)).accesses≤
      6*(∑i:Fin n, rows[i.val].length)+45*n := by
  have he := (sweep_perm a s tie).length_eq
  have ht := htie.length_eq
  simp only [List.length_map,List.length_finRange] at he ht
  have h := construct_accesses rows s (sweep a s tie)
  omega

/-- The pre-bucketing incidence stream is reused by the cardinal-key pass. -/
def classified {n : ℕ} (rows : Vector (List (Fin n)) n) (preferred : Bool)
    (events : List (Event (Fin n))) : List (Fin n × Fin n) × ℕ :=
  let p := build events
  let e := parentEntries p.events
  let a := BatchAdjacency.runList rows e.1
  let f := select preferred e.1 a.1.toList
  (f.1,p.accesses+e.2+a.2+f.2+2*e.1.length)

lemma classified_values {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (s : Bool) (events : List (Event (Fin n))) :
    (classified rows s events).1=(parentEntries (build events).events).1.filter
      (fun p => decide (G.Adj p.1 p.2) != s) := by
  simp only [classified,answers_list G rows hr,select_map]

lemma classified_group {n : ℕ} (rows : Vector (List (Fin n)) n) (s : Bool)
    (events : List (Event (Fin n))) :
    (group (classified rows s events).1).rows=(construct rows s events).rows := rfl

lemma classified_length {n : ℕ} (rows : Vector (List (Fin n)) n) (s : Bool)
    (events : List (Event (Fin n))) : (classified rows s events).1.length≤events.length := by
  have he := parentEntries_bounds (build events).events
  have hf := select_bounds s (parentEntries (build events).events).1
    (BatchAdjacency.runList rows (parentEntries (build events).events).1).1.toList
  have hlen : (build events).events.length=events.length := scan_length 0 events []
  exact hf.1.trans (hlen ▸ he.1)

lemma classified_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (s : Bool) (events : List (Event (Fin n))) :
    (classified rows s events).2≤6*(∑i:Fin n, rows[i.val].length)+29*events.length+6*n := by
  have hp := build_accesses events
  have he := parentEntries_bounds (build events).events
  have ha := BatchAdjacency.runList_accesses rows (parentEntries (build events).events).1
  have hf := select_bounds s (parentEntries (build events).events).1
    (BatchAdjacency.runList rows (parentEntries (build events).events).1).1.toList
  have hlen : (build events).events.length=events.length := scan_length 0 events []
  simp only [classified]
  omega

end HiddenCircuits.DH.NonpreferredHeads
