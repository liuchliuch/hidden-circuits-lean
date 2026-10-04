import HiddenCircuits.DH.SliceHeads

/-! Stable linear bucketing of immediate slice children after the endpoint-stack
pass. All buckets are initialized once, not once per slice. -/
namespace HiddenCircuits.DH.SliceHeads
open LexBFSModel LinearBuckets

/-- Read each parent once and emit at most one directed parent/child incidence. -/
def parentEntries {n : ℕ} : List (ParentEvent (Fin n)) → List (Fin n × Fin n) × ℕ
  | [] => ([],0)
  | p::ps =>
      let q := parentEntries ps
      match p.parent with
      | none => (q.1,q.2+2)
      | some f => ((f.vertex,p.frame.vertex)::q.1,q.2+3)

lemma parentEntries_values {n : ℕ} (ps : List (ParentEvent (Fin n))) :
    (parentEntries ps).1 = ps.filterMap (fun p => p.parent.map (fun f => (f.vertex,p.frame.vertex))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases hp : p.parent <;> simp [parentEntries,hp,ih]

lemma parentEntries_bounds {n : ℕ} (ps : List (ParentEvent (Fin n))) :
    (parentEntries ps).1.length≤ps.length ∧ (parentEntries ps).2≤3*ps.length := by
  induction ps with
  | nil => simp [parentEntries]
  | cons p ps ih => cases hp : p.parent <;> simp [parentEntries,hp] <;> omega

structure Children (n : ℕ) where
  rows : Vector (List (Fin n)) n
  accesses : ℕ

/-- Restore chronological order inside the parent-indexed buckets. -/
def groupParents {n : ℕ} (ps : List (ParentEvent (Fin n))) : Children n :=
  let e := parentEntries ps
  let f := fill Prod.fst e.1 (Vector.replicate n [])
  let q := Adjacency.finish (List.finRange n) f.1
  ⟨⟨q.1.toArray,by simp [q]⟩,e.2+f.2+q.2+3*n⟩

/-- Every immediate-child list has exactly the stable parent-filtered incidences. -/
lemma groupParents_get {n : ℕ} (ps : List (ParentEvent (Fin n))) (i : Fin n) :
    (groupParents ps).rows[i.val] =
      (((parentEntries ps).1.filter (fun p => p.1==i)).map Prod.snd) := by
  simp [groupParents,Adjacency.finish_values,fill_get]

lemma groupParents_accesses {n : ℕ} (ps : List (ParentEvent (Fin n))) :
    (groupParents ps).accesses ≤ 8*ps.length+5*n := by
  let es := (parentEntries ps).1
  let bins := (fill Prod.fst es (Vector.replicate n [])).1
  have hperm : (collect (List.finRange n) bins).1.Perm es := by
    have heq : (collect (List.finRange n).reverse bins).1 = (sort Prod.fst es).1 := rfl
    have hp : (collect (List.finRange n) bins).1.Perm
        (collect (List.finRange n).reverse bins).1 := by
      rw [collect_values,collect_values]
      exact (List.reverse_perm _).symm.flatMap_right _
    rw [heq] at hp
    exact hp.trans (sort_perm Prod.fst es)
  have hlen := hperm.length_eq
  have hbound := parentEntries_bounds ps
  simp only [groupParents,fill_accesses,Adjacency.finish_accesses,List.length_finRange]
  change (parentEntries ps).2+3*es.length+
    (2*(collect (List.finRange n) bins).1.length+2*n)+3*n ≤ _
  change es.length≤ps.length ∧ _ at hbound
  omega

/-- Recover and group all slice child heads using only the compact event stream. -/
def childHeads {n : ℕ} (events : List (Event (Fin n))) : Children n :=
  let p := build events
  let q := groupParents p.events
  ⟨q.rows,p.accesses+q.accesses⟩

lemma childHeads_accesses {n : ℕ} (events : List (Event (Fin n))) :
    (childHeads events).accesses ≤ 17*events.length+5*n := by
  have hp := build_accesses events
  have hq := groupParents_accesses (build events).events
  have he : (build events).events.length=events.length := scan_length 0 events []
  simp only [childHeads]
  omega

/-- Ordinary finite graph sweeps supply both the exact parent semantics and the
linear-size grouped head arrays; no forest is a runtime input. -/
theorem childHeads_sweep_spec {n : ℕ} (a : Fin n → Fin n → Bool) (s : Bool)
    (tie : List (Fin n)) (htie : tie.Perm (List.finRange n)) :
    ParentCorrect [] (build (sweep a s tie)).events ∧
      (childHeads (sweep a s tie)).accesses≤22*n := by
  refine ⟨(build_sweep_spec a s tie).1,?_⟩
  have hlen := (sweep_perm a s tie).length_eq
  have hlen' := htie.length_eq
  simp only [List.length_map,List.length_finRange] at hlen hlen'
  have h := childHeads_accesses (sweep a s tie)
  omega

end HiddenCircuits.DH.SliceHeads
