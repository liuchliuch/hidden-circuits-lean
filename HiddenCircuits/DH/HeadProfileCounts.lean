import HiddenCircuits.DH.BatchAdjacency

/-! Sparse common-neighbor sizes for actual child-head incidences. Each distinct
head contributes one traversal of its original row. A single batched adjacency
pass classifies all generated queries and a direct array accumulates the counts. -/
namespace HiddenCircuits.DH.HeadProfileCounts
open scoped BigOperators
open LinearBuckets

/-- Head label followed by the actual (parent, queried neighbor) pair. -/
abbrev Probe (n : ℕ) := Fin n × (Fin n × Fin n)

def emitRow {n : ℕ} (parent head : Fin n) : List (Fin n) → List (Probe n) × ℕ
  | [] => ([],0)
  | z::zs => let q := emitRow parent head zs; ((head,(parent,z))::q.1,q.2+2)

@[simp] lemma emitRow_values {n : ℕ} (parent head : Fin n) (row : List (Fin n)) :
    (emitRow parent head row).1 = row.map (fun z=>(head,(parent,z))) := by
  induction row <;> simp [emitRow, *]

@[simp] lemma emitRow_accesses {n : ℕ} (parent head : Fin n) (row : List (Fin n)) :
    (emitRow parent head row).2 = 2*row.length := by induction row <;> simp [emitRow, *] <;> omega

/-- Each supplied head causes exactly one original-row read and one row traversal. -/
def expand {n : ℕ} (rows : Vector (List (Fin n)) n) : List (Fin n × Fin n) → List (Probe n) × ℕ
  | [] => ([],0)
  | e::es =>
    let a := emitRow e.1 e.2 rows[e.2.val]
    let q := expand rows es
    (a.1++q.1,a.2+q.2+a.1.length+2)

lemma expand_values {n : ℕ} (rows : Vector (List (Fin n)) n) (heads : List (Fin n × Fin n)) :
    (expand rows heads).1 = heads.flatMap (fun e=>rows[e.2.val].map (fun z=>(e.2,(e.1,z)))) := by
  induction heads <;> simp [expand, *]

lemma expand_length {n : ℕ} (rows : Vector (List (Fin n)) n) (heads : List (Fin n × Fin n)) :
    (expand rows heads).1.length = (heads.map (fun e=>rows[e.2.val].length)).sum := by
  simp [expand_values,List.length_flatMap]

lemma expand_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (heads : List (Fin n × Fin n)) :
    (expand rows heads).2 = 3*(expand rows heads).1.length+2*heads.length := by
  induction heads with
  | nil => simp [expand]
  | cons e es ih => simp [expand,ih]; omega

/-- Unique head labels prevent repeatedly charging the same original adjacency row. -/
theorem expand_length_le {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup) :
    (expand rows heads).1.length ≤ ∑ i : Fin n, rows[i.val].length := by
  rw [expand_length]
  have he : (heads.map (fun e=>rows[e.2.val].length)).sum =
      ∑ i ∈ (heads.map Prod.snd).toFinset, rows[i.val].length := by
    rw [List.sum_toFinset _ hn]
    simp [List.map_map,Function.comp_def]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)

/-- Extract the actual query list in one explicit counted traversal. -/
def queries {n : ℕ} : List (Probe n) → List (Fin n × Fin n) × ℕ
  | [] => ([],0)
  | p::ps => let q := queries ps; (p.2::q.1,q.2+2)

@[simp] lemma queries_values {n : ℕ} (ps : List (Probe n)) : (queries ps).1=ps.map Prod.snd := by
  induction ps <;> simp [queries, *]

@[simp] lemma queries_accesses {n : ℕ} (ps : List (Probe n)) : (queries ps).2=2*ps.length := by
  induction ps <;> simp [queries, *] <;> omega

/-- Every true answer increments its own direct head-indexed counter. -/
def tally {n : ℕ} : List (Probe n) → List Bool → Vector ℕ n → Vector ℕ n × ℕ
  | [],_,counts => (counts,0)
  | _,[],counts => (counts,0)
  | p::ps,yes::answers,counts =>
    let next := if yes then counts.set p.1.val (counts[p.1.val]+1) else counts
    let q := tally ps answers next
    (q.1,q.2+(if yes then 4 else 2))

lemma tally_accesses {n : ℕ} (ps : List (Probe n)) (answers : List Bool) (counts : Vector ℕ n) :
    (tally ps answers counts).2 ≤ 4*ps.length := by
  induction ps generalizing answers counts with
  | nil => simp [tally]
  | cons p ps ih =>
    cases answers with
    | nil => simp [tally]
    | cons yes answers =>
      have h := ih answers (if yes then counts.set p.1.val (counts[p.1.val]+1) else counts)
      cases yes <;> simp only [tally,Bool.false_eq_true,if_false,if_true,List.length_cons] at h ⊢ <;> omega

lemma tally_map_get {n : ℕ} (ps : List (Probe n)) (test : Probe n → Bool)
    (counts : Vector ℕ n) (i : Fin n) :
    (tally ps (ps.map test) counts).1[i.val] = counts[i.val]+
      (ps.filter (fun p=>p.1==i && test p)).length := by
  induction ps generalizing counts with
  | nil => simp [tally]
  | cons p ps ih =>
    by_cases he : p.1=i
    · cases ht : test p <;> simp [tally,ih,he,ht] <;> omega
    · have hval : p.1.val≠i.val := fun hv=>he (Fin.ext hv)
      cases ht : test p <;> simp [tally,ih,he,hval,ht]

lemma answers_list {n : ℕ} (rows : Vector (List (Fin n)) n) (qs : List (Fin n × Fin n)) :
    (BatchAdjacency.runList rows qs).1.toList =
      qs.map (fun p=>decide (p.2∈rows[p.1.val])) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h := BatchAdjacency.runList_get rows qs ⟨i,by simpa using hi⟩
    simpa using h

structure Result (n : ℕ) where
  counts : Vector ℕ n
  accesses : ℕ

/-- Query mapping, list/vector conversions and the input-query length traversal are
charged separately from the existing batched vector engine. -/
def commonCounts {n : ℕ} (rows : Vector (List (Fin n)) n) (heads : List (Fin n × Fin n)) : Result n :=
  let p := expand rows heads
  let q := queries p.1
  let a := BatchAdjacency.runList rows q.1
  let t := tally p.1 a.1.toList (Vector.replicate n 0)
  ⟨t.1,p.2+q.2+a.2+t.2+3*p.1.length+n⟩

lemma commonCounts_value {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (i : Fin n) :
    (commonCounts rows heads).counts[i.val] =
      ((expand rows heads).1.filter
        (fun p=>p.1==i && decide (p.2.2∈rows[p.2.1.val]))).length := by
  simp only [commonCounts,answers_list,queries_values,List.map_map]
  simpa using tally_map_get (expand rows heads).1
    (fun p=>decide (p.2.2∈rows[p.2.1.val])) (Vector.replicate n 0) i

/-- The batch plus accumulation is linear in original incidences and supplied heads. -/
theorem commonCounts_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup) :
    (commonCounts rows heads).accesses ≤
      29*(∑ i : Fin n,rows[i.val].length)+7*n+2*heads.length := by
  have he := expand_accesses rows heads
  have hq := queries_accesses (expand rows heads).1
  have ha := BatchAdjacency.runList_accesses rows (queries (expand rows heads).1).1
  have ht := tally_accesses (expand rows heads).1
    (BatchAdjacency.runList rows (queries (expand rows heads).1).1).1.toList (Vector.replicate n 0)
  have hl := expand_length_le rows heads hn
  simp only [queries_values,List.length_map] at ha
  dsimp only [commonCounts]
  omega

lemma expand_filter_absent {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (i : Fin n) (test : Probe n → Bool)
    (hi : i ∉ heads.map Prod.snd) :
    ((expand rows heads).1.filter (fun p=>p.1==i && test p))=[] := by
  apply List.filter_eq_nil_iff.mpr
  intro p hp
  rw [expand_values] at hp
  obtain ⟨e,he,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
  have hne : e.2≠i := by
    intro hh
    exact hi (List.mem_map.mpr ⟨e,he,hh⟩)
  simp [hne]

/-- Because a head occurs once, its accumulated count comes from exactly its own
original row, tested against its own parent's original neighborhood. -/
lemma commonCounts_list_get {n : ℕ} (rows : Vector (List (Fin n)) n)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup)
    (parent head : Fin n) (hm : (parent,head)∈heads) :
    (commonCounts rows heads).counts[head.val] =
      (rows[head.val].filter (fun z=>decide (z∈rows[parent.val]))).length := by
  rw [commonCounts_value]
  induction heads with
  | nil => simp at hm
  | cons e es ih =>
    have hnd := List.nodup_cons.mp hn
    simp only [List.mem_cons] at hm
    rcases hm with he | hm
    · subst e
      have hz := expand_filter_absent rows es head
        (fun p=>decide (p.2.2∈rows[p.2.1.val])) hnd.1
      simp [expand,List.filter_append,hz,List.filter_map,Function.comp_def]
    · have hne : e.2≠head := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨(parent,head),hm,he.symm⟩)
      have hbe : (e.2==head)=false := by simp [hne]
      simpa [expand,List.filter_append,List.filter_map,Function.comp_def,hbe] using ih hnd.2 hm

/-- Exact graph-theoretic common-neighbor cardinality from ordinary duplicate-free
input adjacency lists and duplicate-free child-head labels. -/
theorem commonCounts_get {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (hrows : ∀ i : Fin n,(rows[i.val]).Nodup)
    (heads : List (Fin n × Fin n)) (hn : (heads.map Prod.snd).Nodup)
    (parent head : Fin n) (hm : (parent,head)∈heads) :
    (commonCounts rows heads).counts[head.val] =
      (G.neighborFinset parent ∩ G.neighborFinset head).card := by
  rw [commonCounts_list_get rows heads hn parent head hm,
    ← List.toFinset_card_of_nodup ((hrows head).filter _)]
  congr 1
  ext z
  simp [List.mem_filter,hr parent z,hr head z,and_comm]

end HiddenCircuits.DH.HeadProfileCounts
