import HiddenCircuits.DH.LexBFSPartition

/-! Counted capacity computation scans ordinary rows without constructing incidence pairs. -/
namespace HiddenCircuits.DH.LexBFSPartition

def measureLength {A : Type*} : List A → Counted ℕ
  | [] => ⟨0,0⟩
  | _::xs => let q := measureLength xs; ⟨q.value+1,q.accesses+1⟩

@[simp] lemma measureLength_value {A : Type*} (xs : List A) : (measureLength xs).value = xs.length := by
  induction xs <;> simp [measureLength, *]

@[simp] lemma measureLength_accesses {A : Type*} (xs : List A) : (measureLength xs).accesses = xs.length := by
  induction xs <;> simp [measureLength, *]

def capacityFrom {n : ℕ} (rows : Vector (List (Fin n)) n) : List (Fin n) → Counted ℕ
  | [] => ⟨0,0⟩
  | i::indices =>
      let row := measureLength rows[i.val]
      let q := capacityFrom rows indices
      ⟨row.value+q.value,row.accesses+q.accesses+2⟩

lemma capacityFrom_spec {n : ℕ} (rows : Vector (List (Fin n)) n) (indices : List (Fin n)) :
    (capacityFrom rows indices).value = (indices.map (fun i => rows[i.val].length)).sum ∧
      (capacityFrom rows indices).accesses =
        (indices.map (fun i => rows[i.val].length)).sum+2*indices.length := by
  induction indices with
  | nil => exact ⟨rfl,rfl⟩
  | cons i indices ih =>
    simp only [capacityFrom,measureLength_value,measureLength_accesses,List.map_cons,List.sum_cons,List.length_cons]
    constructor
    · rw [ih.1]
    · rw [ih.2]; omega

/-- Includes generation of the finite index traversal as well as each row/list-cell read. -/
def capacityScan {n : ℕ} (rows : Vector (List (Fin n)) n) : Counted ℕ :=
  let q := capacityFrom rows (List.finRange n)
  ⟨q.value,q.accesses+n⟩

@[simp] theorem capacityScan_value {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (capacityScan rows).value = LinearBuckets.Adjacency.incidenceCount rows := by
  change (capacityFrom rows (List.finRange n)).value = _
  rw [(capacityFrom_spec rows (List.finRange n)).1]
  simp [LinearBuckets.Adjacency.incidenceCount,LinearBuckets.Adjacency.entriesFrom_values,List.length_flatMap]

@[simp] theorem capacityScan_accesses {n : ℕ} (rows : Vector (List (Fin n)) n) :
    (capacityScan rows).accesses = LinearBuckets.Adjacency.incidenceCount rows+3*n := by
  have hv := capacityScan_value rows
  have hs := capacityFrom_spec rows (List.finRange n)
  change (capacityFrom rows (List.finRange n)).value = _ at hv
  change (capacityFrom rows (List.finRange n)).accesses+n = _
  simp only [List.length_finRange] at hs
  omega

lemma capacityScan_eq {n : ℕ} (rows : Vector (List (Fin n)) n) :
    capacityScan rows = ⟨LinearBuckets.Adjacency.incidenceCount rows,
      LinearBuckets.Adjacency.incidenceCount rows+3*n⟩ := by
  have hv := capacityScan_value rows
  have ha := capacityScan_accesses rows
  cases he : capacityScan rows with
  | mk value accesses =>
    simp only [he] at hv ha
    cases hv
    cases ha
    rfl

end HiddenCircuits.DH.LexBFSPartition
