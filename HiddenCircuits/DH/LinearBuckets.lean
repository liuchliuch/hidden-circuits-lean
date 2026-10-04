import HiddenCircuits.DH.Preprocessing
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Executable stable counting-sort primitives for linear graph preprocessing.
Costs count explicit array accesses and linked-list cell operations. -/
namespace HiddenCircuits.DH.LinearBuckets
variable {α : Type*} {b : ℕ}

/-- Insert input items into their key-indexed array buckets, using constant-time cons. -/
def fill (key : α → Fin b) : List α → Vector (List α) b → Vector (List α) b × ℕ
  | [],bins => (bins,0)
  | a :: xs,bins =>
      let q := fill key xs (bins.set (key a).val (a :: bins[(key a).val]))
      (q.1,q.2+3)

/-- Read each bucket once, restore its original order, and concatenate it once. -/
def collect (indices : List (Fin b)) (bins : Vector (List α) b) : List α × ℕ :=
  match indices with
  | [] => ([],0)
  | i :: indices =>
      let q := collect indices bins
      (bins[i.val].reverse ++ q.1,q.2+2*bins[i.val].length+1)

/-- Stable descending bucket sort with one initialization and one bucket traversal. -/
def sort (key : α → Fin b) (xs : List α) : List α × ℕ :=
  let f := fill key xs (Vector.replicate b [])
  let c := collect (List.finRange b).reverse f.1
  (c.1,f.2+c.2+3*b)

@[simp] lemma fill_accesses (key : α → Fin b) (xs : List α) (bins : Vector (List α) b) :
    (fill key xs bins).2 = 3*xs.length := by
  induction xs generalizing bins with
  | nil => rfl
  | cons a xs ih => simp [fill,ih]; omega

lemma fill_get (key : α → Fin b) (xs : List α) (bins : Vector (List α) b) (i : Fin b) :
    (fill key xs bins).1[i.val] = (xs.filter (fun x => key x == i)).reverse ++ bins[i.val] := by
  induction xs generalizing bins with
  | nil => simp [fill]
  | cons a xs ih =>
    rw [fill,ih]
    by_cases he : key a = i
    · simp [he,List.reverse_cons,List.append_assoc]
    · have hev : (key a).val ≠ i.val := fun h => he (Fin.ext h)
      simp [he,hev]

lemma collect_values (indices : List (Fin b)) (bins : Vector (List α) b) :
    (collect indices bins).1 = indices.flatMap (fun i => bins[i.val].reverse) := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp [collect,ih]

lemma collect_accesses (indices : List (Fin b)) (bins : Vector (List α) b) :
    (collect indices bins).2 = 2*(collect indices bins).1.length+indices.length := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp [collect,ih]; omega

/-- Exact stable-group semantics of the actual bucket-array implementation. -/
theorem sort_values (key : α → Fin b) (xs : List α) :
    (sort key xs).1 = (List.finRange b).reverse.flatMap
      (fun i => xs.filter (fun x => key x == i)) := by
  simp only [sort,collect_values]
  congr 1
  funext i
  simp [fill_get]

/-- Every input occurrence appears exactly once in the sorted output. -/
theorem sort_perm (key : α → Fin b) (xs : List α) : (sort key xs).1.Perm xs := by
  classical
  rw [sort_values,List.perm_iff_count]
  intro a
  rw [List.count_flatMap]
  have hzero (i : Fin b) (hi : i ≠ key a) (hmem : i ∈ (List.finRange b).reverse) :
      ((xs.filter (fun x => key x == i)).count a) = 0 := by
    apply List.count_eq_zero_of_not_mem
    simp [List.mem_filter,Ne.symm hi]
  have hs := List.sum_map_eq_nsmul_single (key a)
    (fun i => ((xs.filter (fun x => key x == i)).count a)) hzero
  change ((List.finRange b).reverse.map (fun i => ((xs.filter (fun x => key x == i)).count a))).sum = _
  rw [hs]
  simp [List.nodup_finRange]

/-- The implemented output has nonincreasing keys. -/
theorem sort_descending (key : α → Fin b) (xs : List α) :
    (sort key xs).1.Pairwise (fun a c => key c ≤ key a) := by
  rw [sort_values,List.pairwise_flatMap]
  constructor
  · intro i hi
    apply List.pairwise_of_forall_mem_list
    intro a ha c hc
    have ha' : key a = i := by simpa using (List.mem_filter.mp ha).2
    have hc' : key c = i := by simpa using (List.mem_filter.mp hc).2
    simp [ha',hc']
  · have hindices : (List.finRange b).reverse.Pairwise (fun i j => j ≤ i) := by
      rw [List.pairwise_reverse,List.finRange,List.pairwise_ofFn]
      exact fun i j h => le_of_lt h
    apply hindices.imp
    intro i j hij a ha c hc
    have ha' : key a = i := by simpa using (List.mem_filter.mp ha).2
    have hc' : key c = j := by simpa using (List.mem_filter.mp hc).2
    simpa [ha',hc'] using hij

/-- Linear explicit operation count for the actual sorting loops. -/
theorem sort_accesses (key : α → Fin b) (xs : List α) :
    (sort key xs).2 = 5*xs.length+4*b := by
  have hlen := (sort_perm key xs).length_eq
  simp only [sort] at hlen ⊢
  rw [fill_accesses,collect_accesses,List.length_reverse,List.length_finRange,hlen]
  omega

lemma filter_key_filter (key : α → Fin b) (xs : List α) (i j : Fin b) :
    (xs.filter (fun x => key x == j)).filter (fun x => key x == i) =
      if j = i then xs.filter (fun x => key x == i) else [] := by
  by_cases h : j = i
  · subst j; simp [List.filter_filter]
  · rw [if_neg h]
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    have hxj : key x = j := by simpa using (List.mem_filter.mp hx).2
    simp [hxj,h]

lemma flatMap_single_bucket (indices : List (Fin b)) (hn : indices.Nodup)
    (i : Fin b) (hi : i ∈ indices) (xs : List α) :
    indices.flatMap (fun j => if j = i then xs else []) = xs := by
  induction indices with
  | nil => simp at hi
  | cons j js ih =>
    obtain ⟨hjn,hn⟩ := List.nodup_cons.mp hn
    by_cases hji : j = i
    · subst j
      have ht : js.flatMap (fun j => if j = i then xs else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro j hj
        have hne : j ≠ i := by intro he; exact hjn (he ▸ hj)
        simp [hne]
      simp [ht]
    · have hi' : i ∈ js := (List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simpa [hji] using ih hn hi'

/-- Stability is an exact preservation of the original equal-key subsequence. -/
theorem sort_stable (key : α → Fin b) (xs : List α) (i : Fin b) :
    ((sort key xs).1.filter (fun x => key x == i)) = xs.filter (fun x => key x == i) := by
  rw [sort_values,List.filter_flatMap]
  simp_rw [filter_key_filter]
  exact flatMap_single_bucket _ (by simpa only [List.nodup_reverse] using List.nodup_finRange b) i
    (by simp) _

/-- A stable bucket pass prepends one lexicographic key to any already sorted
secondary relation. This is the correctness step for linear radix sorting. -/
theorem sort_lex (key : α → Fin b) (xs : List α) (R : α → α → Prop)
    (hR : xs.Pairwise R) :
    (sort key xs).1.Pairwise (fun a c => key c < key a ∨ key c = key a ∧ R a c) := by
  rw [sort_values,List.pairwise_flatMap]
  constructor
  · intro i hi
    apply (hR.filter _).imp_of_mem
    intro a c ha hc hac
    have ha' : key a = i := by simpa using (List.mem_filter.mp ha).2
    have hc' : key c = i := by simpa using (List.mem_filter.mp hc).2
    exact Or.inr ⟨hc'.trans ha'.symm,hac⟩
  · have hindices : (List.finRange b).reverse.Pairwise (fun i j => j < i) := by
      rw [List.pairwise_reverse,List.finRange,List.pairwise_ofFn]
      exact fun _ _ h => h
    apply hindices.imp
    intro i j hij a ha c hc
    have ha' : key a = i := by simpa using (List.mem_filter.mp ha).2
    have hc' : key c = j := by simpa using (List.mem_filter.mp hc).2
    exact Or.inl (by simpa [ha',hc'] using hij)

/-- Three actual stable bucket passes, from least to most significant key. -/
def radix3 (k₁ k₂ k₃ : α → Fin b) (xs : List α) : List α × ℕ :=
  let a := sort k₃ xs
  let b := sort k₂ a.1
  let c := sort k₁ b.1
  (c.1,a.2+b.2+c.2)

theorem radix3_perm (k₁ k₂ k₃ : α → Fin b) (xs : List α) :
    (radix3 k₁ k₂ k₃ xs).1.Perm xs :=
  (sort_perm k₁ _).trans ((sort_perm k₂ _).trans (sort_perm k₃ xs))

theorem radix3_order (k₁ k₂ k₃ : α → Fin b) (xs : List α) :
    (radix3 k₁ k₂ k₃ xs).1.Pairwise (fun a c =>
      k₁ c < k₁ a ∨ k₁ c = k₁ a ∧
        (k₂ c < k₂ a ∨ k₂ c = k₂ a ∧ k₃ c ≤ k₃ a)) :=
  sort_lex k₁ _ _ (sort_lex k₂ _ _ (sort_descending k₃ xs))

theorem radix3_accesses (k₁ k₂ k₃ : α → Fin b) (xs : List α) :
    (radix3 k₁ k₂ k₃ xs).2 = 15*xs.length+12*b := by
  have h₁ := (sort_perm k₃ xs).length_eq
  have h₂ := (sort_perm k₂ (sort k₃ xs).1).length_eq
  simp only [radix3,sort_accesses]
  omega

/-- Measure a list by an actual one-pass traversal. -/
def measureLength : List α → ℕ × ℕ
  | [] => (0,0)
  | _ :: xs => let q := measureLength xs; (q.1+1,q.2+1)

@[simp] lemma measureLength_value (xs : List α) : (measureLength xs).1 = xs.length := by
  induction xs <;> simp [measureLength, *]

@[simp] lemma measureLength_accesses (xs : List α) : (measureLength xs).2 = xs.length := by
  induction xs <;> simp [measureLength, *]

/-- Compute each neighborhood size exactly once, storing its bounded bucket key. -/
def sizeRows {n : ℕ} : (rows : List (List (Fin n))) →
    (∀ row ∈ rows, row.Nodup) → List (Fin (n+1) × List (Fin n)) × ℕ
  | [],_ => ([],0)
  | row :: rows,hn =>
      let l := measureLength row
      let i : Fin (n+1) := ⟨l.1,by
        rw [measureLength_value]
        have h := (hn row (List.mem_cons_self)).length_le_card
        simp only [Fintype.card_fin] at h
        omega⟩
      let q := sizeRows rows (fun r hr => hn r (List.mem_cons_of_mem row hr))
      ((i,row) :: q.1,q.2+l.2+2)

@[simp] lemma sizeRows_projection {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) : (sizeRows rows hn).1.map Prod.snd = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [sizeRows,ih]

lemma sizeRows_keys {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) :
    ∀ p ∈ (sizeRows rows hn).1, p.1.val = p.2.length := by
  induction rows with
  | nil => simp [sizeRows]
  | cons row rows ih =>
    intro p hp
    simp only [sizeRows,List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · exact ih _ p hp

@[simp] lemma sizeRows_length {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) : (sizeRows rows hn).1.length = rows.length := by
  have h := congrArg List.length (sizeRows_projection rows hn)
  simpa only [List.length_map] using h

@[simp] lemma sizeRows_accesses {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) :
    (sizeRows rows hn).2 = LaminarMarking.incidenceCount rows+2*rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp [sizeRows,ih,LaminarMarking.incidenceCount]
    omega

/-- Actual stable size ordering for neighborhood incidence lists. -/
def sortRows {n : ℕ} (rows : List (List (Fin n))) (hn : ∀ row ∈ rows, row.Nodup) :
    List (List (Fin n)) × ℕ :=
  let a := sizeRows rows hn
  let s := sort Prod.fst a.1
  (s.1.map Prod.snd,a.2+s.2+s.1.length)

theorem sortRows_perm {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) : (sortRows rows hn).1.Perm rows := by
  have h := (sort_perm Prod.fst (sizeRows rows hn).1).map Prod.snd
  simpa only [sortRows,sizeRows_projection] using h

theorem sortRows_descending {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) :
    (sortRows rows hn).1.Pairwise (fun a b => b.length ≤ a.length) := by
  change ((sort Prod.fst (sizeRows rows hn).1).1.map Prod.snd).Pairwise _
  rw [List.pairwise_map]
  apply (sort_descending Prod.fst (sizeRows rows hn).1).imp_of_mem
  intro a b ha hb hab
  have ha' := (sort_perm Prod.fst (sizeRows rows hn).1).mem_iff.mp ha
  have hb' := (sort_perm Prod.fst (sizeRows rows hn).1).mem_iff.mp hb
  have hka := sizeRows_keys rows hn a ha'
  have hkb := sizeRows_keys rows hn b hb'
  change b.1.val ≤ a.1.val at hab
  omega

theorem sortRows_accesses {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) :
    (sortRows rows hn).2 = LaminarMarking.incidenceCount rows+8*rows.length+4*(n+1) := by
  have hlen := (sort_perm Prod.fst (sizeRows rows hn).1).length_eq
  simp only [sortRows,sort_accesses,sizeRows_accesses,sizeRows_length] at hlen ⊢
  omega

structure CheckedRows (n : ℕ) where
  ordered : List (List (Fin n))
  accepted : Bool
  accesses : ℕ

/-- Complete incidence-linear size sort followed by the actual laminar marking
checker. The only input proof is the ordinary set-list representation invariant. -/
def checkRows {n : ℕ} (rows : List (List (Fin n))) (hn : ∀ row ∈ rows, row.Nodup) : CheckedRows n :=
  let s := sortRows rows hn
  let c := LaminarMarking.check s.1
  ⟨s.1,c.accepted,s.2+c.accesses⟩

lemma laminar_perm {n : ℕ} {a b : List (List (Fin n))} (h : a.Perm b) :
    LaminarMarking.Laminar a ↔ LaminarMarking.Laminar b := by
  apply h.pairwise_iff
  intro x y hxy
  rcases hxy with hd | hs | hs
  · exact Or.inl hd.symm
  · exact Or.inr (Or.inr hs)
  · exact Or.inr (Or.inl hs)

lemma incidenceCount_perm {n : ℕ} {a b : List (List (Fin n))} (h : a.Perm b) :
    LaminarMarking.incidenceCount a = LaminarMarking.incidenceCount b :=
  (h.map List.length).sum_eq

/-- The source's levelwise laminar checker, including size ordering, is correct
and has an actual linear array/list operation bound. -/
theorem checkRows_spec {n : ℕ} (rows : List (List (Fin n)))
    (hn : ∀ row ∈ rows, row.Nodup) :
    (checkRows rows hn).ordered.Perm rows ∧
    (checkRows rows hn).ordered.Pairwise (fun a b => b.length ≤ a.length) ∧
    ((checkRows rows hn).accepted = true ↔ LaminarMarking.Laminar rows) ∧
    (checkRows rows hn).accesses ≤
      5*LaminarMarking.incidenceCount rows+11*rows.length+5*n+4 := by
  have hp := sortRows_perm rows hn
  have hd := sortRows_descending rows hn
  have hn' : ∀ row ∈ (sortRows rows hn).1, row.Nodup := fun row h => hn row (hp.mem_iff.mp h)
  refine ⟨hp,hd,?_,?_⟩
  · exact (LaminarMarking.check_correct _ hn' hd).trans (laminar_perm hp)
  · have hc := LaminarMarking.check_accesses_le (sortRows rows hn).1
    have hi := incidenceCount_perm hp
    have hl := hp.length_eq
    have hs := sortRows_accesses rows hn
    change (sortRows rows hn).2+(LaminarMarking.check (sortRows rows hn).1).accesses ≤ _
    omega

/-- Convert semantic predecessor laminarity to the literal incidence lists used
by the marking algorithm. -/
theorem predecessor_rows_laminar {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : Fin n) (k : ℕ)
    (vertices : List (Fin n)) (neighbors : Fin n → List (Fin n))
    (hlevel : ∀ v ∈ vertices, G.dist r v = k)
    (hneighbors : ∀ v ∈ vertices, ∀ x, x ∈ neighbors v ↔ x ∈ predecessors G r v) :
    LaminarMarking.Laminar (vertices.map neighbors) := by
  rw [LaminarMarking.Laminar,List.pairwise_map]
  apply List.pairwise_of_forall_mem_list
  intro u hu v hv
  rcases hG.predecessors_laminar hc r u v ((hlevel u hu).trans (hlevel v hv).symm) with hd | hs | hs
  · left
    apply Finset.disjoint_left.mpr
    intro x hxu hxv
    exact Set.disjoint_left.mp hd ((hneighbors u hu x).mp (List.mem_toFinset.mp hxu))
      ((hneighbors v hv x).mp (List.mem_toFinset.mp hxv))
  · right; left
    intro x hx
    exact List.mem_toFinset.mpr ((hneighbors v hv x).mpr
      (hs ((hneighbors u hu x).mp (List.mem_toFinset.mp hx))))
  · right; right
    intro x hx
    exact List.mem_toFinset.mpr ((hneighbors u hu x).mpr
      (hs ((hneighbors v hv x).mp (List.mem_toFinset.mp hx))))

/-- Actual BFS-layer incidence data from a semantic distance-hereditary graph
always passes the implemented checker after the implemented size bucket sort. -/
theorem checkRows_predecessors_accepts {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : DistanceHereditaryGraph G) (hc : G.Connected) (r : Fin n) (k : ℕ)
    (vertices : List (Fin n)) (neighbors : Fin n → List (Fin n))
    (hlevel : ∀ v ∈ vertices, G.dist r v = k)
    (hneighbors : ∀ v ∈ vertices, ∀ x, x ∈ neighbors v ↔ x ∈ predecessors G r v)
    (hn : ∀ row ∈ vertices.map neighbors, row.Nodup) :
    (checkRows (vertices.map neighbors) hn).accepted = true :=
  (checkRows_spec _ hn).2.2.1.mpr
    (predecessor_rows_laminar hG hc r k vertices neighbors hlevel hneighbors)

namespace Adjacency

/-- Expand adjacency lists into (destination,source) incidences in source order. -/
def entriesFrom {n : ℕ} (indices : List (Fin n)) (rows : Vector (List (Fin n)) n) :
    List (Fin n × Fin n) × ℕ :=
  match indices with
  | [] => ([],0)
  | i :: indices =>
      let q := entriesFrom indices rows
      let row := rows[i.val].map (fun x => (x,i))
      (row ++ q.1,q.2+2*rows[i.val].length+1)

lemma entriesFrom_values {n : ℕ} (indices : List (Fin n)) (rows : Vector (List (Fin n)) n) :
    (entriesFrom indices rows).1 = indices.flatMap (fun i => rows[i.val].map (fun x => (x,i))) := by
  induction indices <;> simp [entriesFrom, *]

lemma entriesFrom_accesses {n : ℕ} (indices : List (Fin n)) (rows : Vector (List (Fin n)) n) :
    (entriesFrom indices rows).2 = 2*(entriesFrom indices rows).1.length+indices.length := by
  induction indices <;> simp [entriesFrom, *] <;> omega

/-- Restore the stable order of each incidence bucket and discard its destination tag. -/
def finish {n : ℕ} (indices : List (Fin n)) (bins : Vector (List (Fin n × Fin n)) n) :
    List (List (Fin n)) × ℕ :=
  match indices with
  | [] => ([],0)
  | i :: indices =>
      let q := finish indices bins
      ((bins[i.val].reverse.map Prod.snd) :: q.1,q.2+2*bins[i.val].length+2)

@[simp] lemma finish_values {n : ℕ} (indices : List (Fin n)) (bins : Vector (List (Fin n × Fin n)) n) :
    (finish indices bins).1 = indices.map (fun i => bins[i.val].reverse.map Prod.snd) := by
  induction indices <;> simp [finish, *]

@[simp] lemma finish_length {n : ℕ} (indices : List (Fin n)) (bins : Vector (List (Fin n × Fin n)) n) :
    (finish indices bins).1.length = indices.length := by simp

lemma finish_accesses {n : ℕ} (indices : List (Fin n)) (bins : Vector (List (Fin n × Fin n)) n) :
    (finish indices bins).2 = 2*(collect indices bins).1.length+2*indices.length := by
  induction indices <;> simp [finish,collect, *] <;> omega

structure Result (n : ℕ) where
  rows : Vector (List (Fin n)) n
  accesses : ℕ

/-- Sort all adjacency lists simultaneously by transposing the incidence array.
For an undirected graph, symmetry makes this a sorting of the original neighborhoods. -/
def transpose {n : ℕ} (rows : Vector (List (Fin n)) n) : Result n :=
  let e := entriesFrom (List.finRange n) rows
  let f := fill Prod.fst e.1 (Vector.replicate n [])
  let q := finish (List.finRange n) f.1
  ⟨⟨q.1.toArray,by simp [q]⟩,e.2+f.2+q.2+3*n⟩

/-- Total number of stored input incidences, with multiplicity. -/
def incidenceCount {n : ℕ} (rows : Vector (List (Fin n)) n) : ℕ :=
  (entriesFrom (List.finRange n) rows).1.length

lemma transpose_get {n : ℕ} (rows : Vector (List (Fin n)) n) (i : Fin n) :
    (transpose rows).rows[i.val] =
      (((entriesFrom (List.finRange n) rows).1.filter (fun p => p.1 == i)).map Prod.snd) := by
  simp [transpose,finish_values,fill_get]

lemma entries_sorted {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (entriesFrom (List.finRange n) rows).1.Pairwise (fun a b => a.2 ≤ b.2) := by
  rw [entriesFrom_values,List.pairwise_flatMap]
  constructor
  · intro i hi
    rw [List.pairwise_map]
    exact List.pairwise_of_forall (fun _ _ => le_refl i)
  · have hindices : (List.finRange n).Pairwise (fun i j => i ≤ j) := by
      rw [List.finRange,List.pairwise_ofFn]
      exact fun i j h => le_of_lt h
    apply hindices.imp
    intro i j hij a ha b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    exact hij

/-- Every output neighborhood is ordered increasingly by the original vertex labels. -/
theorem transpose_sorted {n : ℕ} (rows : Vector (List (Fin n)) n) (i : Fin n) :
    ((transpose rows).rows[i.val]).Pairwise (· ≤ ·) := by
  rw [transpose_get,List.pairwise_map]
  exact (entries_sorted rows).filter _

/-- Transposition has exactly the expected incidence semantics. -/
theorem mem_transpose_iff {n : ℕ} (rows : Vector (List (Fin n)) n) (i j : Fin n) :
    j ∈ (transpose rows).rows[i.val] ↔ i ∈ rows[j.val] := by
  rw [transpose_get]
  constructor
  · intro hj
    obtain ⟨p,hp,hpj⟩ := List.mem_map.mp hj
    obtain ⟨hpe,hpi⟩ := List.mem_filter.mp hp
    have hpi' : p.1 = i := by simpa using hpi
    have hpair : p = (i,j) := Prod.ext hpi' hpj
    subst p
    rw [entriesFrom_values] at hpe
    obtain ⟨k,hk,hkp⟩ := List.mem_flatMap.mp hpe
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hkp
    have hxi : x = i := congrArg Prod.fst he
    have hkj : k = j := congrArg Prod.snd he
    subst x
    subst k
    exact hx
  · intro hij
    apply List.mem_map.mpr
    refine ⟨(i,j),List.mem_filter.mpr ⟨?_,by simp⟩,rfl⟩
    rw [entriesFrom_values]
    exact List.mem_flatMap.mpr ⟨j,List.mem_finRange j,List.mem_map.mpr ⟨i,hij,rfl⟩⟩

/-- All graph neighborhoods are simultaneously sorted with a linear number of
explicit incidence-array and list operations. -/
theorem transpose_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (transpose rows).accesses = 7*incidenceCount rows+6*n := by
  let e := (entriesFrom (List.finRange n) rows).1
  let bins := (fill Prod.fst e (Vector.replicate n [])).1
  have hperm : (collect (List.finRange n) bins).1.Perm e := by
    have heq : (collect (List.finRange n).reverse bins).1 = (sort Prod.fst e).1 := rfl
    have hp : (collect (List.finRange n) bins).1.Perm
        (collect (List.finRange n).reverse bins).1 := by
      rw [collect_values,collect_values]
      exact (List.reverse_perm _).symm.flatMap_right _
    rw [heq] at hp
    exact hp.trans (sort_perm Prod.fst e)
  have hl := hperm.length_eq
  change (collect (List.finRange n) bins).1.length = incidenceCount rows at hl
  simp only [transpose,entriesFrom_accesses,fill_accesses,finish_accesses,List.length_finRange]
  change 2*incidenceCount rows+n+3*incidenceCount rows+
    (2*(collect (List.finRange n) bins).1.length+2*n)+3*n = _
  omega

lemma entries_nodup {n : ℕ} (rows : Vector (List (Fin n)) n)
    (hn : ∀ i : Fin n, (rows[i.val]).Nodup) :
    (entriesFrom (List.finRange n) rows).1.Nodup := by
  rw [entriesFrom_values,List.Nodup,List.pairwise_flatMap]
  constructor
  · intro i hi
    exact (hn i).map (fun x y h => congrArg Prod.fst h)
  · apply (List.nodup_finRange n).imp
    intro i j hij a ha b hb he
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    exact hij (congrArg Prod.snd he)

/-- Ordinary duplicate-free adjacency representation is preserved by transposition. -/
theorem transpose_nodup {n : ℕ} (rows : Vector (List (Fin n)) n)
    (hn : ∀ i : Fin n, (rows[i.val]).Nodup) (i : Fin n) :
    ((transpose rows).rows[i.val]).Nodup := by
  rw [transpose_get]
  apply List.Nodup.map_on ?_ ((entries_nodup rows hn).filter _)
  intro a ha b hb he
  have ha' : a.1 = i := by simpa using (List.mem_filter.mp ha).2
  have hb' : b.1 = i := by simpa using (List.mem_filter.mp hb).2
  exact Prod.ext (ha'.trans hb'.symm) he

/-- Membership equivalence to an ordinary undirected input graph. -/
def Represents {n : ℕ} (G : SimpleGraph (Fin n)) (rows : Vector (List (Fin n)) n) : Prop :=
  ∀ i j, j ∈ rows[i.val] ↔ G.Adj i j

/-- The simultaneous linear sorter preserves the unchanged graph represented by
the input adjacency lists. -/
theorem transpose_represents {n : ℕ} (G : SimpleGraph (Fin n))
    (rows : Vector (List (Fin n)) n) (hr : Represents G rows) :
    Represents G (transpose rows).rows := by
  intro i j
  rw [mem_transpose_iff,hr j i,G.adj_comm]

/-- Incidence length agrees with the ordinary graph's degree sum. -/
theorem incidenceCount_eq_degree_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Represents G rows)
    (hn : ∀ i : Fin n, (rows[i.val]).Nodup) :
    incidenceCount rows = ∑ i : Fin n, G.degree i := by
  have hlength (i : Fin n) : (rows[i.val]).length = G.degree i := by
    have he : (rows[i.val]).toFinset = G.neighborFinset i := by
      ext j
      simp only [List.mem_toFinset,SimpleGraph.mem_neighborFinset]
      exact hr i j
    rw [← List.toFinset_card_of_nodup (hn i),he]
    rfl
  simp only [incidenceCount,entriesFrom_values,List.length_flatMap,List.length_map]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  exact Finset.sum_congr rfl (fun i hi => hlength i)

/-- A complete ordinary-graph O(n+m) normalization step, including semantic
preservation, sorted duplicate-free neighborhoods, and explicit operation count. -/
theorem transpose_graph_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rows : Vector (List (Fin n)) n) (hr : Represents G rows)
    (hn : ∀ i : Fin n, (rows[i.val]).Nodup) :
    Represents G (transpose rows).rows ∧
      (∀ i : Fin n, ((transpose rows).rows[i.val]).Nodup ∧
        ((transpose rows).rows[i.val]).Pairwise (· ≤ ·)) ∧
      (transpose rows).accesses = 14*G.edgeFinset.card+6*n := by
  refine ⟨transpose_represents G rows hr,fun i => ⟨transpose_nodup rows hn i,transpose_sorted rows i⟩,?_⟩
  rw [transpose_accesses,incidenceCount_eq_degree_sum G rows hr hn,
    G.sum_degrees_eq_twice_card_edges]
  omega

end Adjacency

end HiddenCircuits.DH.LinearBuckets
