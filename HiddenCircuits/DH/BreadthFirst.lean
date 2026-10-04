import HiddenCircuits.DH.LevelOrdering

/-! Executable layer-synchronous breadth-first search over ordinary adjacency arrays. -/
namespace HiddenCircuits.DH.BreadthFirst
open SimpleGraph
open scoped BigOperators

structure Discovery (n : ℕ) where
  marks : Vector (Option ℕ) n
  next : List (Fin n)
  accesses : ℕ

/-- Mark and enqueue precisely those scanned vertices which have not been seen. -/
def discover {n : ℕ} (level : ℕ) : List (Fin n) → Vector (Option ℕ) n → List (Fin n) → Discovery n
  | [],marks,next => ⟨marks,next,0⟩
  | x :: xs,marks,next =>
      if marks[x.val] = none then
        let q := discover level xs (marks.set x.val (some level)) (x :: next)
        ⟨q.marks,q.next,q.accesses+4⟩
      else
        let q := discover level xs marks next
        ⟨q.marks,q.next,q.accesses+2⟩

lemma discover_accesses {n : ℕ} (level : ℕ) (xs : List (Fin n))
    (marks : Vector (Option ℕ) n) (next : List (Fin n)) :
    (discover level xs marks next).accesses ≤ 4*xs.length := by
  induction xs generalizing marks next with
  | nil => simp [discover]
  | cons x xs ih =>
    simp only [discover]
    split
    · have h := ih (marks.set x.val (some level)) (x :: next)
      simp only [List.length_cons]
      omega
    · have h := ih marks next
      simp only [List.length_cons]
      omega

lemma discover_get {n : ℕ} (level : ℕ) (xs : List (Fin n))
    (marks : Vector (Option ℕ) n) (next : List (Fin n)) (y : Fin n) :
    (discover level xs marks next).marks[y.val] =
      if marks[y.val] = none ∧ y ∈ xs then some level else marks[y.val] := by
  induction xs generalizing marks next with
  | nil => simp [discover]
  | cons x xs ih =>
    by_cases hx : marks[x.val] = none
    · simp only [discover,hx,↓reduceIte,ih,List.mem_cons]
      by_cases hy : y = x
      · subst x
        simp [hx]
      · have hv : x.val ≠ y.val := fun he => hy (Fin.ext he.symm)
        simp [hy,hv]
    · simp only [discover,hx,↓reduceIte,ih,List.mem_cons]
      by_cases hy : y = x
      · subst x
        simp [hx]
      · simp [hy]

lemma discover_next {n : ℕ} (level : ℕ) (xs : List (Fin n))
    (marks : Vector (Option ℕ) n) (next : List (Fin n)) (y : Fin n) :
    y ∈ (discover level xs marks next).next ↔
      y ∈ next ∨ marks[y.val] = none ∧ y ∈ xs := by
  induction xs generalizing marks next with
  | nil => simp [discover]
  | cons x xs ih =>
    by_cases hx : marks[x.val] = none
    · simp only [discover,hx,↓reduceIte,ih,List.mem_cons]
      by_cases hy : y = x
      · subst x; simp [hx]
      · have hv : x.val ≠ y.val := fun he => hy (Fin.ext he.symm)
        simp [hy,hv]
    · simp only [discover,hx,↓reduceIte,ih,List.mem_cons]
      by_cases hy : y = x
      · subst x; simp [hx]
      · simp [hy]

lemma discover_next_marked {n : ℕ} (level : ℕ) (xs : List (Fin n))
    (marks : Vector (Option ℕ) n) (next : List (Fin n))
    (hnext : ∀ y ∈ next, marks[y.val] ≠ none) :
    ∀ y ∈ (discover level xs marks next).next,
      (discover level xs marks next).marks[y.val] ≠ none := by
  intro y hy
  rw [discover_get]
  rcases (discover_next level xs marks next y).mp hy with hy | hy
  · simp [hnext y hy]
  · simp [hy.1,hy.2]

lemma discover_next_nodup {n : ℕ} (level : ℕ) (xs : List (Fin n))
    (marks : Vector (Option ℕ) n) (next : List (Fin n))
    (hnd : next.Nodup) (hnext : ∀ y ∈ next, marks[y.val] ≠ none) :
    (discover level xs marks next).next.Nodup := by
  induction xs generalizing marks next with
  | nil => exact hnd
  | cons x xs ih =>
    by_cases hx : marks[x.val] = none
    · have hnot : x ∉ next := fun hh => hnext x hh hx
      have hnd' : (x :: next).Nodup := List.nodup_cons.mpr ⟨hnot,hnd⟩
      have hnext' : ∀ y ∈ x :: next, (marks.set x.val (some level))[y.val] ≠ none := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp
        · have hyne : y ≠ x := by intro he; exact hnot (he ▸ hy)
          have hv : x.val ≠ y.val := fun he => hyne (Fin.ext he.symm)
          simpa [hv] using hnext y hy
      simpa [discover,hx] using ih (marks.set x.val (some level)) (x :: next) hnd' hnext'
    · simpa [discover,hx] using ih marks next hnd hnext

/-- Read precisely the current frontier's adjacency lists, copying each incidence once. -/
def neighborsFrom {n : ℕ} (rows : Vector (List (Fin n)) n) : List (Fin n) → List (Fin n) × ℕ
  | [] => ([],0)
  | v :: vs =>
      let q := neighborsFrom rows vs
      (rows[v.val] ++ q.1,q.2+rows[v.val].length+1)

lemma neighborsFrom_values {n : ℕ} (rows : Vector (List (Fin n)) n) (vs : List (Fin n)) :
    (neighborsFrom rows vs).1 = vs.flatMap (fun v => rows[v.val]) := by
  induction vs <;> simp [neighborsFrom, *]

lemma neighborsFrom_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (vs : List (Fin n)) :
    (neighborsFrom rows vs).2 = (neighborsFrom rows vs).1.length+vs.length := by
  induction vs <;> simp [neighborsFrom, *] <;> omega

/-- One actual BFS layer expansion, starting with an empty next frontier. -/
def expand {n : ℕ} (rows : Vector (List (Fin n)) n) (level : ℕ)
    (frontier : List (Fin n)) (marks : Vector (Option ℕ) n) : Discovery n :=
  let ns := neighborsFrom rows frontier
  let d := discover (level+1) ns.1 marks []
  ⟨d.marks,d.next,d.accesses+ns.2⟩

lemma expand_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (level : ℕ)
    (frontier : List (Fin n)) (marks : Vector (Option ℕ) n) :
    (expand rows level frontier marks).accesses ≤
      5*(neighborsFrom rows frontier).1.length+frontier.length := by
  have hd := discover_accesses (level+1) (neighborsFrom rows frontier).1 marks []
  simp only [expand,neighborsFrom_accesses]
  omega

lemma expand_marks {n : ℕ} (rows : Vector (List (Fin n)) n) (level : ℕ)
    (frontier : List (Fin n)) (marks : Vector (Option ℕ) n) (y : Fin n) :
    (expand rows level frontier marks).marks[y.val] =
      if marks[y.val] = none ∧ ∃ v ∈ frontier, y ∈ rows[v.val] then some (level+1) else marks[y.val] := by
  simp [expand,discover_get,neighborsFrom_values]

lemma expand_next {n : ℕ} (rows : Vector (List (Fin n)) n) (level : ℕ)
    (frontier : List (Fin n)) (marks : Vector (Option ℕ) n) (y : Fin n) :
    y ∈ (expand rows level frontier marks).next ↔
      marks[y.val] = none ∧ ∃ v ∈ frontier, y ∈ rows[v.val] := by
  simp [expand,discover_next,neighborsFrom_values]

lemma expand_next_nodup {n : ℕ} (rows : Vector (List (Fin n)) n) (level : ℕ)
    (frontier : List (Fin n)) (marks : Vector (Option ℕ) n) :
    (expand rows level frontier marks).next.Nodup :=
  discover_next_nodup _ _ _ _ (by simp) (by simp)

/-- Exact distance semantics of an intermediate BFS layer. -/
structure LayerInvariant {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n) (level : ℕ)
    (marks : Vector (Option ℕ) n) (frontier : List (Fin n)) : Prop where
  marks_eq : ∀ v, marks[v.val] = if G.dist r v ≤ level then some (G.dist r v) else none
  frontier_eq : ∀ v, v ∈ frontier ↔ G.dist r v = level
  nodup : frontier.Nodup

lemma LayerInvariant.new_iff {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    {r : Fin n} {level : ℕ} {marks : Vector (Option ℕ) n} {frontier : List (Fin n)}
    (hi : LayerInvariant G r level marks frontier) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (y : Fin n) :
    (marks[y.val] = none ∧ ∃ v ∈ frontier, y ∈ rows[v.val]) ↔ G.dist r y = level+1 := by
  have hnone : marks[y.val] = none ↔ level < G.dist r y := by
    rw [hi.marks_eq]
    split_ifs <;> simp_all <;> omega
  rw [hnone]
  constructor
  · rintro ⟨hgt,v,hv,hvy⟩
    have hvl := (hi.frontier_eq v).mp hv
    have hadj := (hr v y).mp hvy
    have hbound := hadj.reachable.dist_triangle_right r
    rw [dist_eq_one_iff_adj.mpr hadj] at hbound
    omega
  · intro hy
    obtain ⟨v,hv⟩ := predecessors_nonempty (hc r y) (by omega)
    exact ⟨by omega,v,(hi.frontier_eq v).mpr (by have := hv.2; omega),(hr v y).mpr hv.1⟩

lemma LayerInvariant.expand {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    {r : Fin n} {level : ℕ} {marks : Vector (Option ℕ) n} {frontier : List (Fin n)}
    (hi : LayerInvariant G r level marks frontier) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) :
    LayerInvariant G r (level+1) (expand rows level frontier marks).marks
      (expand rows level frontier marks).next := by
  refine ⟨?_,?_,expand_next_nodup rows level frontier marks⟩
  · intro y
    rw [expand_marks]
    by_cases hnew : marks[y.val] = none ∧ ∃ v ∈ frontier, y ∈ rows[v.val]
    · have he := (hi.new_iff hc rows hr y).mp hnew
      simp [hnew,he]
    · have hne : G.dist r y ≠ level+1 := fun he => hnew ((hi.new_iff hc rows hr y).mpr he)
      rw [if_neg hnew,hi.marks_eq]
      by_cases hd : G.dist r y ≤ level
      · simp [hd,show G.dist r y ≤ level+1 by omega]
      · simp [hd,show ¬G.dist r y ≤ level+1 by omega]
  · intro y
    rw [expand_next]
    exact hi.new_iff hc rows hr y

/-- Fixed linear fuel avoids an unverified termination oracle. Empty layers cost
only one control step; every nonempty vertex layer is processed once. -/
def run {n : ℕ} (rows : Vector (List (Fin n)) n) :
    ℕ → ℕ → List (Fin n) → Vector (Option ℕ) n → Discovery n
  | 0,_,frontier,marks => ⟨marks,frontier,0⟩
  | fuel+1,level,frontier,marks =>
      let e := expand rows level frontier marks
      let q := run rows fuel (level+1) e.next e.marks
      ⟨q.marks,q.next,q.accesses+e.accesses+1⟩

lemma run_invariant {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (fuel level : ℕ) (r : Fin n) (frontier : List (Fin n)) (marks : Vector (Option ℕ) n)
    (hi : LayerInvariant G r level marks frontier) :
    LayerInvariant G r (level+fuel) (run rows fuel level frontier marks).marks
      (run rows fuel level frontier marks).next := by
  induction fuel generalizing level frontier marks with
  | zero => simpa [run] using hi
  | succ fuel ih =>
    have he := hi.expand hc rows hr
    have h := ih (level+1) (expand rows level frontier marks).next (expand rows level frontier marks).marks he
    simpa [run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Shortest paths use distinct vertices, so every finite connected distance is
strictly less than the number of vertices. -/
lemma dist_lt_vertex_count {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected) (r v : Fin n) :
    G.dist r v < n := by
  obtain ⟨p,hpath,hp⟩ := hc.exists_path_of_dist r v
  have h := hpath.length_lt
  simpa only [Fintype.card_fin,hp] using h

def initialMarks {n : ℕ} (r : Fin n) : Vector (Option ℕ) n :=
  (Vector.replicate n none).set r.val (some 0)

lemma initial_invariant {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected) (r : Fin n) :
    LayerInvariant G r 0 (initialMarks r) [r] := by
  refine ⟨?_,?_,by simp⟩
  · intro v
    by_cases hv : v = r
    · subst v; simp [initialMarks]
    · have hrv : r.val ≠ v.val := fun he => hv (Fin.ext he.symm)
      have hd : G.dist r v ≠ 0 := fun he => hv ((hc r v).dist_eq_zero_iff.mp he).symm
      simp [initialMarks,hrv,hd]
  · intro v
    simp only [List.mem_singleton]
    exact ⟨fun he => by rw [he]; simp,fun he => ((hc r v).dist_eq_zero_iff.mp he).symm⟩

lemma run_complete {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows) (r v : Fin n) :
    (run rows n 0 [r] (initialMarks r)).marks[v.val] = some (G.dist r v) := by
  have h := run_invariant hc rows hr n 0 r [r] (initialMarks r) (initial_invariant hc r)
  have hv := h.marks_eq v
  have hlt := dist_lt_vertex_count hc r v
  simpa only [Nat.zero_add,if_pos (Nat.le_of_lt hlt)] using hv

/-- Incidence-plus-vertex work for exactly the vertices in the current frontier. -/
def frontierWeight {n : ℕ} (rows : Vector (List (Fin n)) n) (frontier : List (Fin n)) : ℕ :=
  (frontier.map (fun v => rows[v.val].length+1)).sum

lemma frontierWeight_eq {n : ℕ} (rows : Vector (List (Fin n)) n) (frontier : List (Fin n)) :
    frontierWeight rows frontier = (neighborsFrom rows frontier).1.length+frontier.length := by
  induction frontier with
  | nil => rfl
  | cons v vs ih =>
    change rows[v.val].length+1+frontierWeight rows vs =
      (rows[v.val] ++ (neighborsFrom rows vs).1).length+(vs.length+1)
    rw [List.length_append,ih]
    omega

/-- Remaining graph incidences are a real potential for the BFS work: each
original vertex contributes only until its own distance layer is processed. -/
noncomputable def remainingWeight {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n)
    (rows : Vector (List (Fin n)) n) (level : ℕ) : ℕ :=
  ∑ v : Fin n, if level ≤ G.dist r v then rows[v.val].length+1 else 0

lemma LayerInvariant.frontier_weight {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {level : ℕ} {marks : Vector (Option ℕ) n} {frontier : List (Fin n)}
    (hi : LayerInvariant G r level marks frontier) (rows : Vector (List (Fin n)) n) :
    frontierWeight rows frontier = ∑ v : Fin n, if G.dist r v = level then rows[v.val].length+1 else 0 := by
  have he : frontier.toFinset = Finset.univ.filter (fun v => G.dist r v = level) := by
    ext v
    simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hi.frontier_eq v
  rw [frontierWeight,← List.sum_toFinset _ hi.nodup,he,Finset.sum_filter]

lemma LayerInvariant.remaining_step {n : ℕ} {G : SimpleGraph (Fin n)} {r : Fin n}
    {level : ℕ} {marks : Vector (Option ℕ) n} {frontier : List (Fin n)}
    (hi : LayerInvariant G r level marks frontier) (rows : Vector (List (Fin n)) n) :
    remainingWeight G r rows level = frontierWeight rows frontier+remainingWeight G r rows (level+1) := by
  rw [hi.frontier_weight]
  unfold remainingWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> omega

/-- Sum of row lengths counts every stored incidence exactly once. -/
lemma sum_row_lengths {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (∑ v : Fin n, rows[v.val].length) = LinearBuckets.Adjacency.incidenceCount rows := by
  simp only [LinearBuckets.Adjacency.incidenceCount,LinearBuckets.Adjacency.entriesFrom_values,
    List.length_flatMap,List.length_map]
  rw [← List.ofFn_eq_map,List.sum_ofFn]

lemma remaining_zero {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n)
    (rows : Vector (List (Fin n)) n) :
    remainingWeight G r rows 0 = LinearBuckets.Adjacency.incidenceCount rows+n := by
  simp only [remainingWeight,Nat.zero_le,ite_true,Finset.sum_add_distrib]
  rw [sum_row_lengths]
  simp

/-- Actual BFS loop cost is charged to its distinct distance layers. No
preassigned operation budget or supplied traversal certificate is used. -/
theorem run_accesses {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (fuel level : ℕ) (r : Fin n) (frontier : List (Fin n)) (marks : Vector (Option ℕ) n)
    (hi : LayerInvariant G r level marks frontier) :
    (run rows fuel level frontier marks).accesses ≤ 5*remainingWeight G r rows level+fuel := by
  induction fuel generalizing level frontier marks with
  | zero => simp [run]
  | succ fuel ih =>
    have he := hi.expand hc rows hr
    have htail := ih (level+1) (expand rows level frontier marks).next
      (expand rows level frontier marks).marks he
    have hlocal := expand_accesses rows level frontier marks
    have hw := frontierWeight_eq rows frontier
    have hs := hi.remaining_step rows
    change (run rows fuel (level+1) (expand rows level frontier marks).next
      (expand rows level frontier marks).marks).accesses+
      (expand rows level frontier marks).accesses+1 ≤ _
    omega

structure Result (n : ℕ) where
  depths : Vector (Fin (n+1)) n
  accesses : ℕ

/-- Execute BFS and export bounded numeric depths. Clipping gives a total program
on all adjacency inputs; correctness proves clipping is inactive on connected graphs. -/
def search {n : ℕ} (rows : Vector (List (Fin n)) n) (r : Fin n) : Result n :=
  let q := run rows n 0 [r] (initialMarks r)
  let depths := q.marks.map (fun d => (⟨min (d.getD 0) n,by omega⟩ : Fin (n+1)))
  ⟨depths,q.accesses+2*n+2⟩

/-- The executable depth array is the ordinary graph distance function. -/
theorem search_depths {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows) (r v : Fin n) :
    (search rows r).depths[v.val].val = G.dist r v := by
  have h := run_complete hc rows hr r v
  have hlt := dist_lt_vertex_count hc r v
  simp [search,h,Nat.min_eq_left (Nat.le_of_lt hlt)]

/-- The actual BFS uses a linear number of explicit array and list operations. -/
theorem search_accesses {n : ℕ} {G : SimpleGraph (Fin n)} (hc : G.Connected)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows) (r : Fin n) :
    (search rows r).accesses ≤ 5*LinearBuckets.Adjacency.incidenceCount rows+8*n+2 := by
  have h := run_accesses hc rows hr n 0 r [r] (initialMarks r) (initial_invariant hc r)
  rw [remaining_zero] at h
  simp only [search]
  omega

/-- Ordinary-input BFS correctness and O(n+m) array/list operation count. -/
theorem search_graph_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : G.Connected) (rows : Vector (List (Fin n)) n)
    (hr : LinearBuckets.Adjacency.Represents G rows) (hn : ∀ v : Fin n, (rows[v.val]).Nodup)
    (r : Fin n) :
    (∀ v, (search rows r).depths[v.val].val = G.dist r v) ∧
      (search rows r).accesses ≤ 10*G.edgeFinset.card+8*n+2 := by
  refine ⟨search_depths hc rows hr r,?_⟩
  have h := search_accesses hc rows hr r
  rw [LinearBuckets.Adjacency.incidenceCount_eq_degree_sum G rows hr hn,
    G.sum_degrees_eq_twice_card_edges] at h
  omega

/-- Select previous-level incidences with actual depth-array reads. -/
def filterPrevious {n : ℕ} (depths : Vector (Fin (n+1)) n) (target : ℕ) :
    List (Fin n) → List (Fin n) × ℕ
  | [] => ([],0)
  | x :: xs =>
      let q := filterPrevious depths target xs
      if depths[x.val].val+1 = target then (x :: q.1,q.2+5) else (q.1,q.2+4)

lemma filterPrevious_values {n : ℕ} (depths : Vector (Fin (n+1)) n) (target : ℕ)
    (xs : List (Fin n)) :
    (filterPrevious depths target xs).1 = xs.filter (fun x => decide (depths[x.val].val+1 = target)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : depths[x.val].val+1 = target <;> simp [filterPrevious,ih,h]

lemma filterPrevious_accesses {n : ℕ} (depths : Vector (Fin (n+1)) n) (target : ℕ)
    (xs : List (Fin n)) : (filterPrevious depths target xs).2 ≤ 5*xs.length := by
  induction xs with
  | nil => simp [filterPrevious]
  | cons x xs ih => simp only [filterPrevious]; split <;> simp only [List.length_cons] <;> omega

def previousFrom {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) :
    List (Fin n) → List (List (Fin n)) × ℕ
  | [] => ([],0)
  | v :: vs =>
      let p := filterPrevious depths depths[v.val].val rows[v.val]
      let q := previousFrom depths rows vs
      (p.1 :: q.1,p.2+q.2+3)

lemma previousFrom_values {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (vs : List (Fin n)) :
    (previousFrom depths rows vs).1 = vs.map (fun v =>
      rows[v.val].filter (fun x => decide (depths[x.val].val+1 = depths[v.val].val))) := by
  induction vs <;> simp [previousFrom,filterPrevious_values, *]

lemma previousFrom_accesses {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (vs : List (Fin n)) :
    (previousFrom depths rows vs).2 ≤ 5*(neighborsFrom rows vs).1.length+3*vs.length := by
  induction vs with
  | nil => simp [previousFrom,neighborsFrom]
  | cons v vs ih =>
    have hp := filterPrevious_accesses depths depths[v.val].val rows[v.val]
    simp only [previousFrom,neighborsFrom,List.length_cons,List.length_append]
    omega

structure PreviousResult (n : ℕ) where
  rows : Vector (List (Fin n)) n
  accesses : ℕ

/-- Compute all actual predecessor neighborhoods from the computed depth array. -/
def previous {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) : PreviousResult n :=
  let q := previousFrom depths rows (List.finRange n)
  ⟨⟨q.1.toArray,by simp [q,previousFrom_values]⟩,q.2+2*n⟩

@[simp] lemma previous_get {n : ℕ} (depths : Vector (Fin (n+1)) n)
    (rows : Vector (List (Fin n)) n) (v : Fin n) :
    (previous depths rows).rows[v.val] =
      rows[v.val].filter (fun x => decide (depths[x.val].val+1 = depths[v.val].val)) := by
  simp [previous,previousFrom_values]

lemma previous_nodup {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) :
    ∀ v : Fin n, ((previous depths rows).rows[v.val]).Nodup := by
  intro v
  rw [previous_get]
  exact (hn v).filter _

lemma previous_spec {n : ℕ} {G : SimpleGraph (Fin n)} (r : Fin n)
    (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n)
    (hd : ∀ v, depths[v.val].val = G.dist r v)
    (hr : LinearBuckets.Adjacency.Represents G rows) (v x : Fin n) :
    x ∈ (previous depths rows).rows[v.val] ↔ x ∈ predecessors G r v := by
  simp only [previous_get,List.mem_filter,decide_eq_true_eq,hd,predecessors,Set.mem_setOf_eq]
  rw [hr v x,G.adj_comm]

lemma previous_incidence_le {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) :
    LinearBuckets.Adjacency.incidenceCount (previous depths rows).rows ≤
      LinearBuckets.Adjacency.incidenceCount rows := by
  rw [← sum_row_lengths,← sum_row_lengths]
  apply Finset.sum_le_sum
  intro v hv
  rw [previous_get]
  exact List.length_filter_le _ _

lemma neighbors_all_length {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (neighborsFrom rows (List.finRange n)).1.length = LinearBuckets.Adjacency.incidenceCount rows := by
  rw [neighborsFrom_values]
  simp only [LinearBuckets.Adjacency.incidenceCount,LinearBuckets.Adjacency.entriesFrom_values,
    List.length_flatMap,List.length_map]

lemma previous_accesses {n : ℕ} (depths : Vector (Fin (n+1)) n) (rows : Vector (List (Fin n)) n) :
    (previous depths rows).accesses ≤ 5*LinearBuckets.Adjacency.incidenceCount rows+5*n := by
  have h := previousFrom_accesses depths rows (List.finRange n)
  rw [neighbors_all_length,List.length_finRange] at h
  simp only [previous]
  omega

structure OrderedGraph (n : ℕ) where
  vertices : List (Fin n)
  accesses : ℕ

/-- Ordinary adjacency input is processed by BFS, predecessor extraction, key
scanning and three bounded-key bucket passes. -/
def levelwiseOrder {n : ℕ} (rows : Vector (List (Fin n)) n)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (r : Fin n) : OrderedGraph n :=
  let b := search rows r
  let p := previous b.depths rows
  let k := LevelOrdering.buildKeys b.depths p.rows (previous_nodup b.depths rows hn)
  let o := LevelOrdering.order k.keys
  ⟨o.1,b.accesses+p.accesses+k.accesses+o.2⟩

/-- The graph itself supplies the complete levelwise laminar order. In particular,
no depth array, predecessor list, or ordering certificate is supplied as an input. -/
theorem levelwiseOrder_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : DistanceHereditaryGraph G) (hc : G.Connected)
    (rows : Vector (List (Fin n)) n) (hr : LinearBuckets.Adjacency.Represents G rows)
    (hn : ∀ v : Fin n, (rows[v.val]).Nodup) (r : Fin n) :
    LevelOrdering.IsLevelwiseLaminar G r (levelwiseOrder rows hn r).vertices ∧
      (levelwiseOrder rows hn r).accesses ≤ 26*G.edgeFinset.card+53*n+14 := by
  let d := (search rows r).depths
  let p := (previous d rows).rows
  have hd : ∀ v, d[v.val].val = G.dist r v := search_depths hc rows hr r
  have hp : ∀ v x, x ∈ p[v.val] ↔ x ∈ predecessors G r v := previous_spec r d rows hd hr
  have hn' : ∀ v : Fin n, (p[v.val]).Nodup := previous_nodup d rows hn
  have ho := LevelOrdering.computed_order_spec hG hc r d p hn' hd hp
  refine ⟨ho.1,?_⟩
  have hb := search_accesses hc rows hr r
  have hprev := previous_accesses d rows
  have hinc := previous_incidence_le d rows
  have hsum := ho.2
  have hgraph := LinearBuckets.Adjacency.incidenceCount_eq_degree_sum G rows hr hn
  rw [G.sum_degrees_eq_twice_card_edges] at hgraph
  change (search rows r).accesses+(previous d rows).accesses+
    (LevelOrdering.buildKeys d p hn').accesses+
    (LevelOrdering.order (LevelOrdering.buildKeys d p hn').keys).2 ≤ _
  change LinearBuckets.Adjacency.incidenceCount p ≤ LinearBuckets.Adjacency.incidenceCount rows at hinc
  omega

end HiddenCircuits.DH.BreadthFirst
