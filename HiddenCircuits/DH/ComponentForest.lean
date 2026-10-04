import HiddenCircuits.DH.BreadthFirst

/-! A shared-mark breadth-first forest for ordinary adjacency arrays. Component
traversals stop immediately at an empty frontier. Marks are allocated once for
all roots; there is no per-component full-vertex initialization or scan. -/
namespace HiddenCircuits.DH.ComponentForest
open SimpleGraph BreadthFirst

structure Component (n : ℕ) where
  marks : Vector (Option ℕ) n
  frontier : List (Fin n)
  members : List (Fin n)
  accesses : ℕ
  allocations : ℕ

/-- Every nonempty layer reads its rows, discovers only previously unmarked
vertices, and copies its frontier into the component's output member list. -/
def explore {n : ℕ} (rows : Vector (List (Fin n)) n) :
    ℕ → ℕ → List (Fin n) → Vector (Option ℕ) n → Component n
  | 0,_,frontier,marks => ⟨marks,frontier,[],1,0⟩
  | _+1,_,[],marks => ⟨marks,[],[],1,0⟩
  | fuel+1,level,v::vs,marks =>
      let e := expand rows level (v::vs) marks
      let q := explore rows fuel (level+1) e.next e.marks
      ⟨q.marks,q.frontier,(v::vs)++q.members,
        q.accesses+e.accesses+(v::vs).length+2,
        q.allocations+(neighborsFrom rows (v::vs)).1.length+e.next.length+(v::vs).length+1⟩

def start {n : ℕ} (rows : Vector (List (Fin n)) n) (r : Fin n) (marks : Vector (Option ℕ) n) : Component n :=
  let q := explore rows n 0 [r] (marks.set r.val (some 0))
  ⟨q.marks,q.frontier,q.members,q.accesses+2,q.allocations+1⟩

/-- Set component ownership only for the newly extracted members. -/
def assign {n : ℕ} (r : Fin n) : List (Fin n) → Vector (Fin n) n → Vector (Fin n) n
  | [], owners => owners
  | v::vs, owners => assign r vs (owners.set v.val r)

lemma assign_get {n : ℕ} (r : Fin n) (vs : List (Fin n)) (owners : Vector (Fin n) n) (v : Fin n) :
    (assign r vs owners)[v.val] = if v∈vs then r else owners[v.val] := by
  induction vs generalizing owners with
  | nil => simp [assign]
  | cons w ws ih =>
    simp only [assign,ih,List.mem_cons]
    by_cases hv : v∈ws
    · simp [hv]
    · by_cases he : v=w
      · subst w;simp [hv]
      · have hne : w.val≠v.val := fun h => he (Fin.ext h.symm)
        simp [hv,he,hne]

structure Result (n : ℕ) where
  marks : Vector (Option ℕ) n
  owners : Vector (Fin n) n
  components : List (Fin n × List (Fin n))
  accesses : ℕ
  allocations : ℕ

/-- The outer root scan checks each original vertex exactly once. Already
covered components are skipped by their shared mark-array entry. -/
def scan {n : ℕ} (rows : Vector (List (Fin n)) n) :
    List (Fin n) → Vector (Option ℕ) n → Vector (Fin n) n → Result n
  | [],marks,owners => ⟨marks,owners,[],1,0⟩
  | r::rs,marks,owners =>
      if marks[r.val]=none then
        let c := start rows r marks
        let q := scan rows rs c.marks (assign r c.members owners)
        ⟨q.marks,q.owners,(r,c.members)::q.components,
          q.accesses+c.accesses+2*c.members.length+3,
          q.allocations+c.allocations+1⟩
      else
        let q := scan rows rs marks owners
        ⟨q.marks,q.owners,q.components,q.accesses+2,q.allocations⟩

/-- Empty graphs use an empty `Vector.ofFn id`; no default vertex is assumed. -/
def forest {n : ℕ} (rows : Vector (List (Fin n)) n) : Result n :=
  let q := scan rows (List.finRange n) (Vector.replicate n none) (Vector.ofFn id)
  ⟨q.marks,q.owners,q.components,q.accesses+3*n+2,q.allocations+3*n⟩

/-- Counted final conversion to the existing bounded BFS depth-array interface. -/
def depths {n : ℕ} (q : Result n) : Vector (Fin (n+1)) n :=
  q.marks.map (fun a => ⟨min (a.getD 0) n,by omega⟩)

lemma explore_empty {n : ℕ} (rows : Vector (List (Fin n)) n) (fuel level : ℕ)
    (marks : Vector (Option ℕ) n) : explore rows fuel level [] marks = ⟨marks,[],[],1,0⟩ := by
  cases fuel <;> rfl

lemma frontierWeight_append {n : ℕ} (rows : Vector (List (Fin n)) n) (xs ys : List (Fin n)) :
    frontierWeight rows (xs++ys) = frontierWeight rows xs+frontierWeight rows ys := by
  simp [frontierWeight]

/-- Actual nonempty-layer work is charged to precisely the rows that are
visited, plus one final empty/fuel test. Graph correctness will show uniqueness. -/
theorem explore_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) (fuel level : ℕ)
    (frontier : List (Fin n)) (marks : Vector (Option ℕ) n) :
    (explore rows fuel level frontier marks).accesses ≤
      5*frontierWeight rows (explore rows fuel level frontier marks).members+1 := by
  induction fuel generalizing level frontier marks with
  | zero => simp [explore,frontierWeight]
  | succ fuel ih =>
    cases frontier with
    | nil => simp [explore,frontierWeight]
    | cons v vs =>
      have ht := ih (level+1) (expand rows level (v::vs) marks).next (expand rows level (v::vs) marks).marks
      have he := expand_accesses rows level (v::vs) marks
      have hw := frontierWeight_eq rows (v::vs)
      simp only [explore,frontierWeight_append,List.length_cons] at *
      omega

lemma discover_next_length {n : ℕ} (level : ℕ) (xs : List (Fin n))
    (marks : Vector (Option ℕ) n) (next : List (Fin n)) :
    (discover level xs marks next).next.length ≤ xs.length+next.length := by
  induction xs generalizing marks next with
  | nil => simp [discover]
  | cons v vs ih =>
    simp only [discover]
    split
    · have h := ih (marks.set v.val (some level)) (v::next)
      simp only [List.length_cons] at *;omega
    · have h := ih marks next
      simp only [List.length_cons] at *;omega

lemma discover_accesses_lower {n : ℕ} (level : ℕ) (xs : List (Fin n))
    (marks : Vector (Option ℕ) n) (next : List (Fin n)) :
    2*xs.length ≤ (discover level xs marks next).accesses := by
  induction xs generalizing marks next with
  | nil => simp [discover]
  | cons v vs ih =>
    simp only [discover]
    split
    · have h := ih (marks.set v.val (some level)) (v::next)
      simp only [List.length_cons] at *;omega
    · have h := ih marks next
      simp only [List.length_cons] at *;omega

/-- Fresh neighbor-list, frontier and member-list cells are explicitly counted;
they are bounded by the charged actual operations. -/
theorem explore_allocations {n : ℕ} (rows : Vector (List (Fin n)) n) (fuel level : ℕ)
    (frontier : List (Fin n)) (marks : Vector (Option ℕ) n) :
    (explore rows fuel level frontier marks).allocations ≤ (explore rows fuel level frontier marks).accesses := by
  induction fuel generalizing level frontier marks with
  | zero => simp [explore]
  | succ fuel ih =>
    cases frontier with
    | nil => simp [explore]
    | cons v vs =>
      have ht := ih (level+1) (expand rows level (v::vs) marks).next (expand rows level (v::vs) marks).marks
      have hn := discover_next_length (level+1) (neighborsFrom rows (v::vs)).1 marks []
      have hl := discover_accesses_lower (level+1) (neighborsFrom rows (v::vs)).1 marks []
      have hrow := neighborsFrom_accesses rows (v::vs)
      simp only [List.length_nil,Nat.add_zero] at hn
      simp only [explore,expand] at *
      omega

end HiddenCircuits.DH.ComponentForest
