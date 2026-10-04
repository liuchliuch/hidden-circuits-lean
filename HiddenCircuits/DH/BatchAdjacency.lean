import HiddenCircuits.DH.LinearBuckets

/-! Sparse batched adjacency queries using one reusable marker array and source buckets. -/
namespace HiddenCircuits.DH.BatchAdjacency
open scoped BigOperators
variable {n q : ℕ}

def mark (value : Bool) : List (Fin n) → Vector Bool n → Vector Bool n × ℕ
  | [],m => (m,0)
  | v::vs,m => let r := mark value vs (m.set v.val value); (r.1,r.2+3)

@[simp] theorem mark_accesses (value : Bool) (vs : List (Fin n)) (m : Vector Bool n) :
    (mark value vs m).2=3*vs.length := by induction vs generalizing m <;> simp [mark, *] <;> omega

theorem mark_get (value : Bool) (vs : List (Fin n)) (m : Vector Bool n) (j : Fin n) :
    (mark value vs m).1[j.val]=if j∈vs then value else m[j.val] := by
  induction vs generalizing m with
  | nil => simp [mark]
  | cons v vs ih =>
    rw [mark,ih]
    by_cases hv:v=j <;> by_cases hj:j∈vs
    all_goals simp [hv,hj]
    all_goals have hv' : v.val≠j.val := fun h => hv (Fin.ext h)
    all_goals simp [hv',Ne.symm hv]

 theorem clear_marks (vs : List (Fin n)) :
    (mark false vs (mark true vs (Vector.replicate n false)).1).1=Vector.replicate n false := by
  apply Vector.ext
  intro i hi
  have hf := mark_get false vs (mark true vs (Vector.replicate n false)).1 ⟨i,hi⟩
  have ht := mark_get true vs (Vector.replicate n false) ⟨i,hi⟩
  rw [hf,ht]
  by_cases hm : (⟨i,hi⟩ : Fin n)∈vs <;> simp [hm]

def answer (queries : Vector (Fin n × Fin n) q) (m : Vector Bool n) :
    List (Fin q) → Vector Bool q → Vector Bool q × ℕ
  | [],a => (a,0)
  | k::ks,a => let r := answer queries m ks (a.set k.val m[(queries[k.val]).2.val]); (r.1,r.2+4)

@[simp] theorem answer_accesses (queries : Vector (Fin n × Fin n) q) (m : Vector Bool n)
    (ks : List (Fin q)) (a : Vector Bool q) : (answer queries m ks a).2=4*ks.length := by
  induction ks generalizing a <;> simp [answer, *] <;> omega

theorem answer_get (queries : Vector (Fin n × Fin n) q) (m : Vector Bool n)
    (ks : List (Fin q)) (a : Vector Bool q) (j : Fin q) :
    (answer queries m ks a).1[j.val]=if j∈ks then m[(queries[j.val]).2.val] else a[j.val] := by
  induction ks generalizing a with
  | nil => simp [answer]
  | cons k ks ih =>
    rw [answer,ih]
    by_cases hk:k=j <;> by_cases hj:j∈ks
    all_goals simp [hk,hj]
    all_goals have hk' : k.val≠j.val := fun h => hk (Fin.ext h)
    all_goals simp [hk',Ne.symm hk]

def buckets (queries : Vector (Fin n × Fin n) q) : Vector (List (Fin q)) n :=
  (LinearBuckets.fill (fun k : Fin q => (queries[k.val]).1) (List.finRange q) (Vector.replicate n [])).1

theorem buckets_mem (queries : Vector (Fin n × Fin n) q) (i : Fin n) (k : Fin q) :
    k∈(buckets queries)[i.val] ↔ (queries[k.val]).1=i := by
  simp [buckets,LinearBuckets.fill_get]

structure State (n q : ℕ) where
  marks : Vector Bool n
  answers : Vector Bool q

def rowStep (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (bs : Vector (List (Fin q)) n) (i : Fin n) (s : State n q) : State n q × ℕ :=
  let m := mark true rows[i.val] s.marks
  let a := answer queries m.1 bs[i.val] s.answers
  let z := mark false rows[i.val] m.1
  (⟨z.1,a.1⟩,m.2+a.2+z.2+4)

theorem rowStep_marks (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (bs : Vector (List (Fin q)) n) (i : Fin n) (a : Vector Bool q) :
    (rowStep rows queries bs i ⟨Vector.replicate n false,a⟩).1.marks=Vector.replicate n false :=
  clear_marks _

theorem rowStep_get (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (i : Fin n) (a : Vector Bool q) (k : Fin q) :
    (rowStep rows queries (buckets queries) i ⟨Vector.replicate n false,a⟩).1.answers[k.val]=
      if (queries[k.val]).1=i then decide ((queries[k.val]).2∈rows[i.val]) else a[k.val] := by
  simp only [rowStep,answer_get,mark_get]
  by_cases hi:(queries[k.val]).1=i
  · rw [if_pos ((buckets_mem queries i k).mpr hi),if_pos hi]
    simp
  · rw [if_neg (fun h => hi ((buckets_mem queries i k).mp h)),if_neg hi]

@[simp] theorem rowStep_accesses (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (bs : Vector (List (Fin q)) n) (i : Fin n) (s : State n q) :
    (rowStep rows queries bs i s).2=6*rows[i.val].length+4*bs[i.val].length+4 := by
  simp [rowStep];omega

def sweep (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (bs : Vector (List (Fin q)) n) : List (Fin n) → State n q → State n q × ℕ
  | [],s => (s,0)
  | i::is,s => let a := rowStep rows queries bs i s; let r := sweep rows queries bs is a.1; (r.1,a.2+r.2)

theorem sweep_marks (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (bs : Vector (List (Fin q)) n) (is : List (Fin n)) (s : State n q) (hs : s.marks=Vector.replicate n false) :
    (sweep rows queries bs is s).1.marks=Vector.replicate n false := by
  induction is generalizing s with
  | nil => exact hs
  | cons i is ih =>
    apply ih
    cases s with | mk m a => simp only at hs; subst m; exact rowStep_marks _ _ _ _ _

theorem sweep_get (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (is : List (Fin n)) (s : State n q) (hs : s.marks=Vector.replicate n false) (k : Fin q) :
    (sweep rows queries (buckets queries) is s).1.answers[k.val]=
      if (queries[k.val]).1∈is then decide ((queries[k.val]).2∈rows[(queries[k.val]).1.val]) else s.answers[k.val] := by
  induction is generalizing s with
  | nil => simp [sweep]
  | cons i is ih =>
    cases s with | mk m a =>
      simp only at hs
      subst m
      rw [sweep,ih _ (rowStep_marks _ _ _ _ _),rowStep_get]
      by_cases hi:(queries[k.val]).1=i <;> by_cases hm:(queries[k.val]).1∈is <;> simp [hi,hm]

 theorem sweep_accesses (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q)
    (bs : Vector (List (Fin q)) n) (is : List (Fin n)) (s : State n q) :
    (sweep rows queries bs is s).2=
      6*(is.map (fun i => rows[i.val].length)).sum+4*(is.map (fun i => bs[i.val].length)).sum+4*is.length := by
  induction is generalizing s <;> simp [sweep, *]; ring


theorem buckets_total (queries : Vector (Fin n × Fin n) q) :
    (∑ i : Fin n, (buckets queries)[i.val].length)=q := by
  let key := fun k : Fin q => (queries[k.val]).1
  have hp : (LinearBuckets.sort key (List.finRange q)).1.length=q := by
    simpa using (LinearBuckets.sort_perm key (List.finRange q)).length_eq
  change (LinearBuckets.collect (List.finRange n).reverse (buckets queries)).1.length=q at hp
  rw [LinearBuckets.collect_values,List.length_flatMap] at hp
  simp only [List.length_reverse,List.map_reverse,List.sum_reverse] at hp
  rw [←List.ofFn_eq_map,List.sum_ofFn] at hp
  exact hp

/-- Marker/result initialization, query-ID generation and source-key lookup are charged explicitly. -/
def run (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q) : State n q × ℕ :=
  let b := LinearBuckets.fill (fun k : Fin q => (queries[k.val]).1) (List.finRange q) (Vector.replicate n [])
  let r := sweep rows queries b.1 (List.finRange n) ⟨Vector.replicate n false,Vector.replicate q false⟩
  (r.1,r.2+b.2+4*q+2*n)

theorem run_get (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q) (k : Fin q) :
    (run rows queries).1.answers[k.val]=decide ((queries[k.val]).2∈rows[(queries[k.val]).1.val]) := by
  exact (sweep_get rows queries (List.finRange n)
    ⟨Vector.replicate n false,Vector.replicate q false⟩ rfl k).trans (by simp)

theorem run_marks (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q) :
    (run rows queries).1.marks=Vector.replicate n false :=
  sweep_marks _ _ _ _ _ rfl

/-- Exact linear access count in vertices, actual adjacency entries, and query occurrences. -/
theorem run_accesses (rows : Vector (List (Fin n)) n) (queries : Vector (Fin n × Fin n) q) :
    (run rows queries).2=6*(∑ i : Fin n,rows[i.val].length)+11*q+6*n := by
  change (sweep rows queries (buckets queries) (List.finRange n) _).2+
    (LinearBuckets.fill _ (List.finRange q) _).2+4*q+2*n=_
  rw [sweep_accesses,LinearBuckets.fill_accesses]
  simp only [←List.ofFn_eq_map,List.sum_ofFn,List.length_finRange]
  rw [buckets_total]
  ring

/-- The user-facing list form preserves the input query order exactly. -/
def runList (rows : Vector (List (Fin n)) n) (queries : List (Fin n × Fin n)) :
    Vector Bool queries.length × ℕ :=
  let r := run rows ⟨queries.toArray,by simp⟩
  (r.1.answers,r.2)

theorem runList_get (rows : Vector (List (Fin n)) n) (queries : List (Fin n × Fin n))
    (k : Fin queries.length) :
    (runList rows queries).1[k.val]=decide ((queries.get k).2∈rows[(queries.get k).1.val]) := by
  simpa [runList] using run_get rows (⟨queries.toArray,by simp⟩ : Vector (Fin n × Fin n) queries.length) k

theorem runList_accesses (rows : Vector (List (Fin n)) n) (queries : List (Fin n × Fin n)) :
    (runList rows queries).2=6*(∑ i : Fin n,rows[i.val].length)+11*queries.length+6*n :=
  run_accesses rows _

theorem runList_graph (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (queries : List (Fin n × Fin n)) (k : Fin queries.length) :
    (runList rows queries).1[k.val]=decide (G.Adj (queries.get k).1 (queries.get k).2) := by
  rw [runList_get]
  congr 1
  exact propext (hr _ _)

end HiddenCircuits.DH.BatchAdjacency

