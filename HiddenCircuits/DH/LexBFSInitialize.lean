import HiddenCircuits.DH.LexBFSCellOrder

/-! Linear direct-array initialization of the numeric tie-order partition. -/
namespace HiddenCircuits.DH.LexBFSPartition
open LexBFSLinks

/-- Initial arrays are allocated and filled once; no adjacency or partition scan is hidden. -/
def blank (n b : ℕ) : Heap n b :=
  ⟨⟨Vector.replicate n none,Vector.replicate n none⟩,
   ⟨Vector.replicate b none,Vector.replicate b none⟩,
   Vector.replicate n none,Vector.replicate b none,Vector.replicate b none,
   Vector.replicate b 0,Vector.replicate b 0,Vector.replicate b none,none,0⟩

/-- Reserve slot zero for the initial (temporarily empty) cell. -/
def seed (n b : ℕ) (hb : 0 < b) : Heap n b :=
  {blank n b with first := some ⟨0,hb⟩,fresh := 1}

lemma seed_vertexView (n b : ℕ) (hb : 0 < b) : VertexView (seed n b hb) (fun _ => []) := by
  constructor
  · simp
  · intro c; trivial
  · intro v c; simp [seed,blank]
  · intro c; simp [seed,blank]
  · intro c; simp [seed,blank]
  · intro c; simp [seed,blank]

lemma seed_cellView (n b : ℕ) (hb : 0 < b) : CellView (seed n b hb) [⟨0,hb⟩] := by
  constructor
  · simp
  · simp [Realizes,Forward,seed,blank]
  · rfl

/-- Append an input traversal into one cell using the proved constant-time primitive. -/
def appendAll {n b : ℕ} (c : Fin b) : List (Fin n) → Heap n b → Counted (Heap n b)
  | [],s => ⟨s,0⟩
  | v::vs,s =>
    let a := appendVertex s c v
    let q := appendAll c vs a.value
    ⟨q.value,a.accesses+q.accesses+1⟩

theorem appendAll_view {n b : ℕ} {s : Heap n b} {f : CellContents n b}
    (h : VertexView s f) (c : Fin b) (xs : List (Fin n)) (hn : xs.Nodup)
    (hfree : ∀ v ∈ xs, s.owner[v.val] = none) :
    VertexView (appendAll c xs s).value (Function.update f c (f c++xs)) := by
  induction xs generalizing s f with
  | nil => simpa [appendAll] using h
  | cons v vs ih =>
    have hv := hfree v List.mem_cons_self
    have ha := appendVertex_view h c v hv
    have hf : ∀ w ∈ vs, (appendVertex s c v).value.owner[w.val] = none := by
      intro w hw
      have hvw : v.val ≠ w.val := by
        intro he
        exact (List.nodup_cons.mp hn).1 (Fin.ext he ▸ hw)
      simpa [appendVertex,hvw] using hfree w (List.mem_cons_of_mem _ hw)
    have ht := ih ha (List.nodup_cons.mp hn).2 hf
    simpa [appendAll,List.append_assoc] using ht

lemma appendAll_order {n b : ℕ} {s : Heap n b} {cs : List (Fin b)}
    (h : CellView s cs) (c : Fin b) (xs : List (Fin n)) :
    CellView (appendAll c xs s).value cs := by
  induction xs generalizing s with
  | nil => exact h
  | cons v vs ih => exact ih (h.appendVertex c v)

lemma appendAll_accesses {n b : ℕ} (c : Fin b) (xs : List (Fin n)) (s : Heap n b) :
    (appendAll c xs s).accesses ≤ 11*xs.length := by
  induction xs generalizing s with
  | nil => simp [appendAll]
  | cons v vs ih =>
    have ha := appendVertex_accesses s c v
    have ht := ih (appendVertex s c v).value
    simp only [appendAll,List.length_cons]
    omega

/-- Initialize in numeric rank order. The temporary `finRange` list is allocated and
traversed once; its allocation is charged separately from the three vertex arrays.
The output state stores no copy of the tie list. -/
def initialHeap (n b : ℕ) (hb : 0 < b) : Counted (Heap n b) :=
  let q := appendAll ⟨0,hb⟩ (List.finRange n) (seed n b hb)
  ⟨{q.value with first := if n = 0 then none else q.value.first},q.accesses+4*n+7*b⟩

def initialContents (n b : ℕ) (hb : 0 < b) : CellContents n b :=
  Function.update (fun _ => []) ⟨0,hb⟩ (List.finRange n)

theorem initialHeap_vertexView (n b : ℕ) (hb : 0 < b) :
    VertexView (initialHeap n b hb).value (initialContents n b hb) := by
  have h := appendAll_view (seed_vertexView n b hb) ⟨0,hb⟩ (List.finRange n)
    (List.nodup_finRange n) (by intro v hv; simp [seed,blank])
  exact ⟨h.nodup,h.links,h.owner,h.head,h.tail,h.size⟩

theorem initialHeap_cellView (n b : ℕ) (hb : 0 < b) :
    CellView (initialHeap n b hb).value (if n = 0 then [] else [⟨0,hb⟩]) := by
  have h := appendAll_order (seed_cellView n b hb) ⟨0,hb⟩ (List.finRange n)
  by_cases hn : n = 0
  · subst n
    refine ⟨by simp,⟨trivial,trivial⟩,?_⟩
    simp [initialHeap]
  · refine ⟨by simp [hn],?_,?_⟩
    · simpa [initialHeap,hn] using h.links
    · simpa [initialHeap,hn] using h.first

theorem initialHeap_accesses (n b : ℕ) (hb : 0 < b) :
    (initialHeap n b hb).accesses ≤ 15*n+7*b := by
  have h := appendAll_accesses (n := n) ⟨0,hb⟩ (List.finRange n) (seed n b hb)
  simp only [List.length_finRange] at h
  dsimp only [initialHeap]
  omega

lemma appendAll_frame {n b : ℕ} (c : Fin b) (xs : List (Fin n)) (s : Heap n b) :
    (appendAll c xs s).value.cells = s.cells ∧
    (appendAll c xs s).value.first = s.first ∧
    (appendAll c xs s).value.fresh = s.fresh ∧
    (appendAll c xs s).value.stamp = s.stamp ∧
    (appendAll c xs s).value.companion = s.companion := by
  induction xs generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons v vs ih => exact ih (appendVertex s c v).value

@[simp] lemma initialHeap_fresh (n b : ℕ) (hb : 0 < b) :
    (initialHeap n b hb).value.fresh = 1 :=
  (appendAll_frame ⟨0,hb⟩ (List.finRange n) (seed n b hb)).2.2.1

@[simp] lemma initialHeap_stamp (n b : ℕ) (hb : 0 < b) :
    (initialHeap n b hb).value.stamp = Vector.replicate b 0 :=
  (appendAll_frame ⟨0,hb⟩ (List.finRange n) (seed n b hb)).2.2.2.1

@[simp] lemma initialHeap_companion (n b : ℕ) (hb : 0 < b) :
    (initialHeap n b hb).value.companion = Vector.replicate b none :=
  (appendAll_frame ⟨0,hb⟩ (List.finRange n) (seed n b hb)).2.2.2.2

lemma initialContents_support (n b : ℕ) (hb : 0 < b) (c : Fin b) :
    initialContents n b hb c ≠ [] ↔ c = ⟨0,hb⟩ ∧ n ≠ 0 := by
  by_cases hc : c = ⟨0,hb⟩
  · subst c
    simp [initialContents]
  · simp [initialContents,Function.update,hc]

end HiddenCircuits.DH.LexBFSPartition
