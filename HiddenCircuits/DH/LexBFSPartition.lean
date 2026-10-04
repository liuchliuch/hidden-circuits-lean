import HiddenCircuits.DH.LexBFSLinks

/-! Direct-pointer stable ordered-partition refinement. Vertex nodes and cell nodes
are stored in separate finite arrays. The row loop reads original adjacency entries only;
its flag controls which side of a touched cell receives the neighbor block. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

/-- All variable-size collections used during a sweep are intrusive lists in arrays.
Cell slots are allocated monotonically; at most one slot is requested per input incidence. -/
structure Heap (n b : ℕ) where
  vertices : Links n
  cells : Links b
  owner : Vector (Option (Fin b)) n
  head : Vector (Pointer n) b
  tail : Vector (Pointer n) b
  size : Vector ℕ b
  stamp : Vector ℕ b
  companion : Vector (Option (Fin b)) b
  first : Pointer b
  fresh : ℕ

structure Counted (α : Type*) where
  value : α
  accesses : ℕ

/-- Remove a cell from the cell order. No vertex or other cell is scanned. -/
def removeCell {n b : ℕ} (s : Heap n b) (c : Fin b) : Counted (Heap n b) :=
  let right := s.cells.next[c.val]
  let links := unlink s.cells c
  ⟨{s with cells := links,first := if s.first = some c then right else s.first},
    1+unlinkAccesses s.cells c⟩

/-- Detach one vertex from its known owner. Empty cells are removed immediately. -/
def removeVertex {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) : Counted (Heap n b) :=
  let left := s.vertices.prev[v.val]
  let right := s.vertices.next[v.val]
  let oldSize := s.size[c.val]
  let t := {s with
    vertices := unlink s.vertices v
    owner := s.owner.set v.val none
    head := if left = none then s.head.set c.val right else s.head
    tail := if right = none then s.tail.set c.val left else s.tail
    size := s.size.set c.val (oldSize-1)}
  let q := if oldSize = 1 then removeCell t c else ⟨t,0⟩
  ⟨q.value,3+unlinkAccesses s.vertices v+2+
    (if left = none then 1 else 0)+(if right = none then 1 else 0)+q.accesses⟩

/-- Append to a known cell in constant time, including the first element of a new cell. -/
def appendVertex {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) : Counted (Heap n b) :=
  let last := s.tail[c.val]
  let oldSize := s.size[c.val]
  ⟨{s with
      vertices := insert s.vertices last none v
      owner := s.owner.set v.val (some c)
      head := if last = none then s.head.set c.val (some v) else s.head
      tail := s.tail.set c.val (some v)
      size := s.size.set c.val (oldSize+1)},
    2+insertAccesses last none+3+(if last = none then 1 else 0)⟩

/-- Allocate the neighbor companion immediately before or after its source cell.
The failure branch is only a totalization; capacity correctness is proved separately. -/
def newCompanion {n b : ℕ} (s : Heap n b) (c : Fin b) (epoch : ℕ) (first : Bool) :
    Counted (Option (Fin b) × Heap n b) :=
  if hf : s.fresh < b then
    let d : Fin b := ⟨s.fresh,hf⟩
    let left := if first then s.cells.prev[c.val] else some c
    let right := if first then some c else s.cells.next[c.val]
    ⟨(some d,{s with
      cells := insert s.cells left right d
      head := s.head.set d.val none
      tail := s.tail.set d.val none
      size := s.size.set d.val 0
      stamp := s.stamp.set c.val epoch
      companion := s.companion.set c.val (some d)
      first := if first && s.first == some c then some d else s.first
      fresh := s.fresh+1}),1+insertAccesses left right+5⟩
  else ⟨(none,s),0⟩

/-- One listed neighbor is ignored if already selected; otherwise it is moved to the
current neighbor companion of its old cell. The graph complement is never queried. -/
def moveNeighbor {n b : ℕ} (s : Heap n b) (epoch : ℕ) (first : Bool) (v : Fin n) :
    Counted (Heap n b) :=
  match s.owner[v.val] with
  | none => ⟨s,1⟩
  | some c =>
    let q := if s.stamp[c.val] = epoch then ⟨(s.companion[c.val],s),1⟩
      else newCompanion s c epoch first
    match q.value.1 with
    | none => ⟨q.value.2,2+q.accesses⟩
    | some d =>
      let r := removeVertex q.value.2 c v
      let a := appendVertex r.value d v
      ⟨a.value,2+q.accesses+r.accesses+a.accesses⟩

/-- The actual sparse refinement loop, processing just one original input row. -/
def refineRow {n b : ℕ} (epoch : ℕ) (first : Bool) :
    List (Fin n) → Heap n b → Counted (Heap n b)
  | [],s => ⟨s,0⟩
  | v::vs,s =>
    let a := moveNeighbor s epoch first v
    let q := refineRow epoch first vs a.value
    ⟨q.value,a.accesses+q.accesses+1⟩

/-- Reading the selected cell size is one direct array read, independent of slice size. -/
def pop {n b : ℕ} (s : Heap n b) : Counted (Option (LexBFSModel.Event (Fin n)) × Heap n b) :=
  match s.first with
  | none => ⟨(none,s),0⟩
  | some c => match s.head[c.val] with
    | none => ⟨(none,s),1⟩
    | some v =>
      let k := s.size[c.val]
      let q := removeVertex s c v
      ⟨(some ⟨v,k⟩,q.value),2+q.accesses⟩

/-- Compact output: the selected vertex and its integer slice length only. -/
structure Result (n b : ℕ) where
  heap : Heap n b
  events : List (LexBFSModel.Event (Fin n))
  accesses : ℕ

/-- Bounded executable sweep. The adjacency-vector row is read exactly once per pivot. -/
def run {n b : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool) :
    ℕ → ℕ → Heap n b → Result n b
  | 0,_,s => ⟨s,[],0⟩
  | fuel+1,epoch,s =>
    let p := pop s
    match p.value.1 with
    | none => ⟨p.value.2,[],p.accesses⟩
    | some e =>
      let r := refineRow epoch first rows[e.vertex.val] p.value.2
      let q := run rows first fuel (epoch+1) r.value
      ⟨q.heap,e::q.events,p.accesses+1+r.accesses+q.accesses+1⟩

lemma removeCell_accesses {n b : ℕ} (s : Heap n b) (c : Fin b) :
    (removeCell s c).accesses ≤ 5 := by
  have h := unlinkAccesses_le s.cells c
  simp only [removeCell]
  omega

lemma removeVertex_accesses {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (removeVertex s c v).accesses ≤ 16 := by
  have h := unlinkAccesses_le s.vertices v
  have hc := unlinkAccesses_le s.cells c
  dsimp only [removeVertex,removeCell]
  split_ifs <;> dsimp only <;> omega

lemma appendVertex_accesses {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (appendVertex s c v).accesses ≤ 10 := by
  have h := insertAccesses_le s.tail[c.val] (none : Pointer n)
  dsimp only [appendVertex]
  split_ifs <;> omega

lemma newCompanion_accesses {n b : ℕ} (s : Heap n b) (c : Fin b) (epoch : ℕ) (first : Bool) :
    (newCompanion s c epoch first).accesses ≤ 10 := by
  unfold newCompanion
  split
  · have h := insertAccesses_le (if first then s.cells.prev[c.val] else some c)
      (if first then some c else s.cells.next[c.val])
    simp only [Counted.accesses]
    omega
  · simp

lemma moveNeighbor_accesses {n b : ℕ} (s : Heap n b) (epoch : ℕ) (first : Bool) (v : Fin n) :
    (moveNeighbor s epoch first v).accesses ≤ 38 := by
  unfold moveNeighbor
  split
  · simp
  · rename_i c hc
    let q : Counted (Option (Fin b) × Heap n b) :=
      if s.stamp[c.val] = epoch then ⟨(s.companion[c.val],s),1⟩
      else newCompanion s c epoch first
    have hq : q.accesses ≤ 10 := by
      dsimp only [q]
      split_ifs
      · norm_num
      · exact newCompanion_accesses s c epoch first
    change (match q.value.1 with
      | none => Counted.mk q.value.2 (2+q.accesses)
      | some d => let r := removeVertex q.value.2 c v
                  let a := appendVertex r.value d v
                  Counted.mk a.value (2+q.accesses+r.accesses+a.accesses)).accesses ≤ 38
    split
    · dsimp only; omega
    · rename_i d hd
      have hr := removeVertex_accesses q.value.2 c v
      have ha := appendVertex_accesses (removeVertex q.value.2 c v).value d v
      dsimp only
      omega

lemma refineRow_accesses {n b : ℕ} (row : List (Fin n)) (s : Heap n b) (epoch : ℕ) (first : Bool) :
    (refineRow epoch first row s).accesses ≤ 39*row.length := by
  induction row generalizing s with
  | nil => simp [refineRow]
  | cons v vs ih =>
    have ha := moveNeighbor_accesses s epoch first v
    have hq := ih (moveNeighbor s epoch first v).value
    simp only [refineRow,List.length_cons]
    omega

end HiddenCircuits.DH.LexBFSPartition
