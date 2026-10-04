import HiddenCircuits.DH.LexBFSPartition

/-! Compositional accounting for the actual direct-pointer sweep. -/
namespace HiddenCircuits.DH.LexBFSPartition

lemma pop_accesses {n b : ℕ} (s : Heap n b) : (pop s).accesses ≤ 18 := by
  unfold pop
  split
  · simp
  · rename_i c hc
    split
    · simp
    · rename_i v hv
      have h := removeVertex_accesses s c v
      dsimp only
      omega

/-- Every event charges only its selected vertex's original adjacency row. -/
def rowWork {n : ℕ} (rows : Vector (List (Fin n)) n)
    (events : List (LexBFSModel.Event (Fin n))) : ℕ :=
  (events.map (fun e => rows[e.vertex.val].length)).sum

/-- A fully operational bound before semantic uniqueness is used: the only nonconstant
step charge is the number of actual entries in the pivot's input row. -/
theorem run_accesses {n b : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (fuel epoch : ℕ) (s : Heap n b) :
    (run rows first fuel epoch s).accesses ≤
      20*fuel+39*rowWork rows (run rows first fuel epoch s).events := by
  induction fuel generalizing s epoch with
  | zero => simp [run,rowWork]
  | succ fuel ih =>
    have hp := pop_accesses s
    cases he : (pop s).value.1 with
    | none => simp [run,he,rowWork]; omega
    | some e =>
      have hr := refineRow_accesses rows[e.vertex.val] (pop s).value.2 epoch first
      have ht := ih (epoch+1) (refineRow epoch first rows[e.vertex.val] (pop s).value.2).value
      simp only [run,he]
      simp only [rowWork,List.map_cons,List.sum_cons] at ht ⊢
      omega

/-- Cell-slot allocation requests are monotone and occur only while processing one
listed input vertex. -/
lemma newCompanion_fresh {n b : ℕ} (s : Heap n b) (c : Fin b) (epoch : ℕ) (first : Bool) :
    s.fresh ≤ (newCompanion s c epoch first).value.2.fresh ∧
      (newCompanion s c epoch first).value.2.fresh ≤ s.fresh+1 := by
  unfold newCompanion
  split <;> simp

@[simp] lemma removeCell_fresh {n b : ℕ} (s : Heap n b) (c : Fin b) :
    (removeCell s c).value.fresh = s.fresh := rfl

@[simp] lemma removeVertex_fresh {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (removeVertex s c v).value.fresh = s.fresh := by
  dsimp only [removeVertex]
  split_ifs <;> rfl

@[simp] lemma appendVertex_fresh {n b : ℕ} (s : Heap n b) (c : Fin b) (v : Fin n) :
    (appendVertex s c v).value.fresh = s.fresh := rfl

lemma moveNeighbor_fresh {n b : ℕ} (s : Heap n b) (epoch : ℕ) (first : Bool) (v : Fin n) :
    s.fresh ≤ (moveNeighbor s epoch first v).value.fresh ∧
      (moveNeighbor s epoch first v).value.fresh ≤ s.fresh+1 := by
  unfold moveNeighbor
  split
  · simp
  · rename_i c hc
    have hf := newCompanion_fresh s c epoch first
    split <;> dsimp only <;> split <;>
      simp only [Counted.value,removeVertex_fresh,appendVertex_fresh] <;> omega

lemma refineRow_fresh {n b : ℕ} (row : List (Fin n)) (s : Heap n b) (epoch : ℕ) (first : Bool) :
    s.fresh ≤ (refineRow epoch first row s).value.fresh ∧
      (refineRow epoch first row s).value.fresh ≤ s.fresh+row.length := by
  induction row generalizing s with
  | nil => simp [refineRow]
  | cons v vs ih =>
    have ha := moveNeighbor_fresh s epoch first v
    have ht := ih (moveNeighbor s epoch first v).value
    simp only [refineRow,List.length_cons]
    constructor <;> omega

@[simp] lemma pop_fresh {n b : ℕ} (s : Heap n b) : (pop s).value.2.fresh = s.fresh := by
  unfold pop
  split
  · rfl
  · split
    · rfl
    · dsimp only; exact removeVertex_fresh _ _ _

/-- Actual allocated cell IDs never exceed one allocation per listed incidence. -/
theorem run_fresh {n b : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (fuel epoch : ℕ) (s : Heap n b) :
    s.fresh ≤ (run rows first fuel epoch s).heap.fresh ∧
      (run rows first fuel epoch s).heap.fresh ≤
        s.fresh+rowWork rows (run rows first fuel epoch s).events := by
  induction fuel generalizing epoch s with
  | zero => simp [run,rowWork]
  | succ fuel ih =>
    cases he : (pop s).value.1 with
    | none => simp [run,he,rowWork]
    | some e =>
      have hr := refineRow_fresh rows[e.vertex.val] (pop s).value.2 epoch first
      have ht := ih (epoch+1) (refineRow epoch first rows[e.vertex.val] (pop s).value.2).value
      simp only [pop_fresh] at hr
      simp only [run,he,rowWork,List.map_cons,List.sum_cons] at ht ⊢
      constructor <;> omega

/-- The output stores at most one vertex/size pair per pivot; it contains no partition
snapshots and no copied selected-cell lists. -/
theorem run_events_length {n b : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (fuel epoch : ℕ) (s : Heap n b) : (run rows first fuel epoch s).events.length ≤ fuel := by
  induction fuel generalizing epoch s with
  | zero => simp [run]
  | succ fuel ih =>
    cases he : (pop s).value.1 with
    | none => simp [run,he]
    | some e =>
      have ht := ih (epoch+1) (refineRow epoch first rows[e.vertex.val] (pop s).value.2).value
      simpa [run,he] using Nat.succ_le_succ ht

lemma rowWork_perm {n : ℕ} (rows : Vector (List (Fin n)) n)
    (events : List (LexBFSModel.Event (Fin n)))
    (hp : (events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) :
    rowWork rows events = LinearBuckets.Adjacency.incidenceCount rows := by
  have he := (hp.map (fun v => rows[v.val].length)).sum_eq
  simpa [rowWork,List.map_map,LinearBuckets.Adjacency.incidenceCount,
    LinearBuckets.Adjacency.entriesFrom_values,List.length_flatMap,List.length_map] using he

/-- The final amortization step uses only vertex uniqueness from semantic refinement.
Every original adjacency entry is then charged once, including the complement sweep. -/
theorem run_accesses_of_perm {n b : ℕ} (rows : Vector (List (Fin n)) n) (first : Bool)
    (epoch : ℕ) (s : Heap n b)
    (hp : ((run rows first n epoch s).events.map LexBFSModel.Event.vertex).Perm (List.finRange n)) :
    (run rows first n epoch s).accesses ≤
      20*n+39*LinearBuckets.Adjacency.incidenceCount rows := by
  simpa [rowWork_perm rows _ hp] using run_accesses rows first n epoch s

end HiddenCircuits.DH.LexBFSPartition
