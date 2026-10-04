import HiddenCircuits.DH.HeadProfileCounts
import HiddenCircuits.DH.CographStaircase

/-! Compute all initial normal/complement weave choices in one sparse adjacency batch.
Only first list cells are read; each root emits at most one original-graph query. -/
namespace HiddenCircuits.DH.FirstHeadChoices
open scoped BigOperators
open LinearBuckets

abbrev Request (n : ℕ) := Fin n × (Fin n × Fin n)

def gather {n : ℕ} (normal complementary : Vector (List (Fin n)) n) :
    List (Fin n) → List (Request n) × ℕ
  | [] => ([],0)
  | r::rs =>
      let q := gather normal complementary rs
      match normal[r.val],complementary[r.val] with
      | a::_,b::_ => ((r,(a,b))::q.1,q.2+6)
      | _,_ => (q.1,q.2+5)

lemma gather_roots {n : ℕ} (normal complementary : Vector (List (Fin n)) n)
    (roots : List (Fin n)) :
    ((gather normal complementary roots).1.map Prod.fst) =
      roots.filter (fun r=>!normal[r.val].isEmpty && !complementary[r.val].isEmpty) := by
  induction roots with
  | nil => rfl
  | cons r rs ih =>
    cases hn : normal[r.val] <;> cases hc : complementary[r.val] <;> simp [gather,hn,hc,ih]

lemma gather_length_le {n : ℕ} (normal complementary : Vector (List (Fin n)) n)
    (roots : List (Fin n)) : (gather normal complementary roots).1.length≤roots.length := by
  have h := List.length_filter_le (fun r:Fin n=>!normal[r.val].isEmpty && !complementary[r.val].isEmpty) roots
  rw [←gather_roots,List.length_map] at h
  exact h

lemma gather_accesses {n : ℕ} (normal complementary : Vector (List (Fin n)) n)
    (roots : List (Fin n)) : (gather normal complementary roots).2≤6*roots.length := by
  induction roots with
  | nil => simp [gather]
  | cons r rs ih =>
    cases hn : normal[r.val] <;> cases hc : complementary[r.val] <;> simp [gather,hn,hc] <;> omega

lemma gather_mem {n : ℕ} (normal complementary : Vector (List (Fin n)) n)
    (roots : List (Fin n)) (r a b : Fin n) :
    (r,(a,b))∈(gather normal complementary roots).1 ↔
      r∈roots ∧ normal[r.val].head?=some a ∧ complementary[r.val].head?=some b := by
  induction roots with
  | nil => simp [gather]
  | cons j js ih =>
    by_cases hrj : r=j
    · subst r
      cases hn : normal[j.val] <;> cases hc : complementary[j.val] <;>
        simp [gather,hn,hc,ih,eq_comm]
    · cases hn : normal[j.val] <;> cases hc : complementary[j.val] <;>
        simp [gather,hn,hc,ih,hrj,Ne.symm hrj]

/-- Write the negated answer to its recorded root; no graph query occurs here. -/
def scatter {n : ℕ} : List (Request n) → List Bool → Vector Bool n → Vector Bool n × ℕ
  | [],_,choices => (choices,0)
  | _,[],choices => (choices,0)
  | p::ps,answer::answers,choices =>
      let q := scatter ps answers (choices.set p.1.val (!answer))
      (q.1,q.2+3)

lemma scatter_accesses {n : ℕ} (ps : List (Request n)) (answers : List Bool) (choices : Vector Bool n) :
    (scatter ps answers choices).2≤3*ps.length := by
  induction ps generalizing answers choices with
  | nil => simp [scatter]
  | cons p ps ih =>
    cases answers with
    | nil => simp [scatter]
    | cons a answers =>
      have h := ih answers (choices.set p.1.val (!a))
      simp only [scatter,List.length_cons]
      omega

lemma scatter_map_absent {n : ℕ} (ps : List (Request n)) (test : Request n → Bool)
    (choices : Vector Bool n) (r : Fin n) (hr : r∉ps.map Prod.fst) :
    (scatter ps (ps.map test) choices).1[r.val]=choices[r.val] := by
  induction ps generalizing choices with
  | nil => rfl
  | cons p ps ih =>
    have hne : p.1.val≠r.val := by
      intro he
      exact hr (List.mem_map.mpr ⟨p,List.mem_cons_self,Fin.ext he⟩)
    have ht : r∉ps.map Prod.fst := fun hm=>hr (List.mem_cons_of_mem _ hm)
    rw [List.map_cons,scatter,ih _ ht]
    simp [hne]

lemma scatter_map_get {n : ℕ} (ps : List (Request n)) (test : Request n → Bool)
    (choices : Vector Bool n) (hn : (ps.map Prod.fst).Nodup)
    (r a b : Fin n) (hm : (r,(a,b))∈ps) :
    (scatter ps (ps.map test) choices).1[r.val] = !test (r,(a,b)) := by
  induction ps generalizing choices with
  | nil => simp at hm
  | cons p ps ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | hm
    · subst p
      rw [List.map_cons,scatter,scatter_map_absent _ _ _ _ hnd.1]
      simp
    · exact ih _ hnd.2 hm

structure Result (n : ℕ) where
  choices : Vector Bool n
  accesses : ℕ

/-- The original graph is queried once in a batch. Index-list allocation, the default
choice array, query projection and list/vector conversions are all charged. -/
def construct {n : ℕ} (rows : Vector (List (Fin n)) n)
    (normal complementary : Vector (List (Fin n)) n) : Result n :=
  let g := gather normal complementary (List.finRange n)
  let q := HeadProfileCounts.queries g.1
  let a := BatchAdjacency.runList rows q.1
  let s := scatter g.1 a.1.toList (Vector.replicate n false)
  ⟨s.1,g.2+q.2+a.2+s.2+3*g.1.length+2*n⟩

lemma construct_answers {n : ℕ} (rows : Vector (List (Fin n)) n)
    (normal complementary : Vector (List (Fin n)) n) :
    (construct rows normal complementary).choices =
      (scatter (gather normal complementary (List.finRange n)).1
        ((gather normal complementary (List.finRange n)).1.map
          (fun p=>decide (p.2.2∈rows[p.2.1.val]))) (Vector.replicate n false)).1 := by
  simp [construct,HeadProfileCounts.answers_list,List.map_map,Function.comp_def]

/-- Actual first-pair choices, including the explicit false default when either side is empty. -/
theorem construct_get {n : ℕ} (rows : Vector (List (Fin n)) n)
    (normal complementary : Vector (List (Fin n)) n) (r : Fin n) :
    (construct rows normal complementary).choices[r.val] =
      match normal[r.val],complementary[r.val] with
      | a::_,b::_ => !decide (b∈rows[a.val])
      | _,_ => false := by
  rw [construct_answers]
  let ps := (gather normal complementary (List.finRange n)).1
  have hn : (ps.map Prod.fst).Nodup := by
    rw [gather_roots]
    exact (List.nodup_finRange n).filter _
  have hmissing (hr : normal[r.val]=[] ∨ complementary[r.val]=[]) : r∉ps.map Prod.fst := by
    intro hm
    obtain ⟨⟨root,a,b⟩,hp,he⟩ := List.mem_map.mp hm
    dsimp only at he
    subst root
    have hh := (gather_mem normal complementary (List.finRange n) r a b).mp hp
    rcases hr with hr | hr <;> simp [hr] at hh
  cases hnormal : normal[r.val] with
  | nil =>
    have hh := scatter_map_absent ps (fun p=>decide (p.2.2∈rows[p.2.1.val]))
      (Vector.replicate n false) r (hmissing (Or.inl hnormal))
    simpa [hnormal] using hh
  | cons a as =>
    cases hcompl : complementary[r.val] with
    | nil =>
      have hh := scatter_map_absent ps (fun p=>decide (p.2.2∈rows[p.2.1.val]))
        (Vector.replicate n false) r (hmissing (Or.inr hcompl))
      simpa [hcompl] using hh
    | cons b bs =>
      have hm : (r,(a,b))∈ps := (gather_mem normal complementary (List.finRange n) r a b).mpr
        ⟨List.mem_finRange r,by simp [hnormal],by simp [hcompl]⟩
      exact scatter_map_get ps _ _ hn r a b hm

/-- Every stored root choice satisfies the exact staircase interface needed by weaving. -/
theorem construct_headChoice {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Adjacency.Represents G rows)
    (normal complementary : Vector (List (Fin n)) n) (r : Fin n) :
    CographStaircase.HeadChoice G.Adj (construct rows normal complementary).choices[r.val]
      normal[r.val] complementary[r.val] := by
  rw [construct_get]
  cases hn : normal[r.val] with
  | nil => trivial
  | cons a as =>
    cases hc : complementary[r.val] with
    | nil => trivial
    | cons b bs => simp [CographStaircase.HeadChoice,hr a b]

/-- At most one first-head query per vertex; complement density never appears. -/
theorem construct_accesses {n : ℕ} (rows : Vector (List (Fin n)) n)
    (normal complementary : Vector (List (Fin n)) n) :
    (construct rows normal complementary).accesses≤6*(∑ i : Fin n,rows[i.val].length)+33*n := by
  have hg := gather_accesses normal complementary (List.finRange n)
  have hlen := gather_length_le normal complementary (List.finRange n)
  have hq := HeadProfileCounts.queries_accesses (gather normal complementary (List.finRange n)).1
  have ha := BatchAdjacency.runList_accesses rows
    (HeadProfileCounts.queries (gather normal complementary (List.finRange n)).1).1
  have hs := scatter_accesses (gather normal complementary (List.finRange n)).1
    (BatchAdjacency.runList rows (HeadProfileCounts.queries
      (gather normal complementary (List.finRange n)).1).1).1.toList (Vector.replicate n false)
  simp only [List.length_finRange] at hg hlen
  simp only [HeadProfileCounts.queries_values,List.length_map] at ha
  dsimp only [construct]
  omega

end HiddenCircuits.DH.FirstHeadChoices
