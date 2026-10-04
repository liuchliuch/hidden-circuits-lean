import HiddenCircuits.Complexity.GridRuntime.Program

/-! Explicit pure prefix states for instantiating the actual nested grid program. -/
namespace HiddenCircuits.Complexity.GridRuntime
variable {k : ℕ}

 theorem foldRow_succ_end (f : ℕ → ℕ → Frame k → Frame k) (i s r : ℕ) (d : Frame k) :
    foldRow f i s (r+1) d=f i (s+r) (foldRow f i s r d) := by
  induction r generalizing s d with
  | zero => rfl
  | succ r ih =>
    simpa only [foldRow,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (s+1) (f i s d)

def rowPrefix (f : ℕ → ℕ → Frame k → Frame k) (m : ℕ) (d : Frame k) : ℕ → Frame k
  | 0 => d
  | i+1 => foldRow f i 0 (m+1) (rowPrefix f m d i)

def prefixStates (f : ℕ → ℕ → Frame k → Frame k) (m : ℕ) (d : Frame k) (i j : ℕ) : Frame k :=
  foldRow f i 0 j (rowPrefix f m d i)

@[simp] theorem prefixStates_zero (f : ℕ → ℕ → Frame k → Frame k) (m : ℕ) (d : Frame k) :
    prefixStates f m d 0 0=d := rfl

theorem prefixStates_succ (f : ℕ → ℕ → Frame k → Frame k) (m : ℕ) (d : Frame k) (i j : ℕ) :
    prefixStates f m d i (j+1)=f i j (prefixStates f m d i j) := by
  simpa [prefixStates] using foldRow_succ_end f i 0 j (rowPrefix f m d i)

theorem prefixStates_row (f : ℕ → ℕ → Frame k → Frame k) (m : ℕ) (d : Frame k) (i : ℕ) :
    prefixStates f m d i (m+1)=prefixStates f m d (i+1) 0 := rfl

theorem foldRow_eq_foldl (f : ℕ → ℕ → Frame k → Frame k) (i s r : ℕ) (d : Frame k) :
    foldRow f i s r d=(List.range' s r).foldl (fun d j => f i j d) d := by
  induction r generalizing s d with
  | zero => rfl
  | succ r ih => simp only [foldRow,List.range'_succ,List.foldl_cons,ih]

theorem rowPrefix_eq_foldl (f : ℕ → ℕ → Frame k → Frame k) (m : ℕ) (d : Frame k) (r : ℕ) :
    rowPrefix f m d r=(List.range r).foldl
      (fun d i => (List.range (m+1)).foldl (fun d j => f i j d) d) d := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [rowPrefix,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,
      ih,foldRow_eq_foldl,←List.range_eq_range']

def gridIndices (n m : ℕ) : List (ℕ × ℕ) :=
  (List.range (n+1)).flatMap (fun i => (List.range (m+1)).map (fun j => (i,j)))

 theorem gridIndices_length (n m : ℕ) : (gridIndices n m).length=(n+1)*(m+1) := by
  simp [gridIndices,List.length_flatMap,Function.comp_def]

theorem rowPrefix_eq_gridFold (f : ℕ → ℕ → Frame k → Frame k) (n m : ℕ) (d : Frame k) :
    rowPrefix f m d (n+1)=(gridIndices n m).foldl (fun d ij => f ij.1 ij.2 d) d := by
  rw [rowPrefix_eq_foldl]
  simp [gridIndices,List.foldl_flatMap,List.foldl_map]

/-- A checked body operation need only be verified on reachable prefix frames.
This is the ordinary composition rule used with bounded integer accumulators. -/
theorem program_fold_executes (B : OracleBlock (k+8)) (g : BitString → ℕ) (n m C : ℕ)
    (f : ℕ → ℕ → Frame k → Frame k) (d : Frame k)
    (hB : ∀ i j, i≤n → j≤m → ∀ inner outer, ∃ c,
      B.Executes g (store n m i j inner outer (prefixStates f m d i j))
        (store n m i j inner outer (f i j (prefixStates f m d i j))) c ∧ c≤C) :
    ∃ c, (program B).Executes g (initialStore n m d)
      (initialStore n m (rowPrefix f m d (n+1))) c ∧ c≤programCost n m C := by
  apply program_executes B g n m C (prefixStates f m d)
  · intro i j hi hj inner outer
    rw [prefixStates_succ]
    exact hB i j hi hj inner outer
  · intro i hi
    exact prefixStates_row f m d i
end HiddenCircuits.Complexity.GridRuntime
