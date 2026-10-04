import HiddenCircuits.Complexity.OracleBitPrograms

/-! A six-label binary incrementer, including exact operational cost and
correctness for the actual natural-number encoding used by oracle answers. -/
namespace HiddenCircuits.Complexity.BitPrograms

def incrementBits : BitString → BitString
  | [] => [true]
  | false::xs => true::xs
  | true::xs => false::incrementBits xs

def leadingOnes : BitString → ℕ
  | true::xs => leadingOnes xs+1
  | _ => 0

lemma leadingOnes_le_length (xs : BitString) : leadingOnes xs ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [leadingOnes] <;> omega

lemma increment_encodePosNum (n : PosNum) :
    incrementBits (Computability.encodePosNum n) = Computability.encodePosNum n.succ := by
  induction n <;> simp [Computability.encodePosNum,PosNum.succ,incrementBits, *]

lemma increment_encodeNum (n : Num) :
    incrementBits (Computability.encodeNum n) = Computability.encodeNum n.succ := by
  cases n <;> simp [Computability.encodeNum,Num.succ,Num.succ',incrementBits,increment_encodePosNum,Computability.encodePosNum]

@[simp] theorem increment_encodeNat (n : ℕ) :
    incrementBits (Computability.encodeNat n) = Computability.encodeNat (n+1) := by
  simp only [Computability.encodeNat,increment_encodeNum]
  congr 1
  rw [Nat.cast_add,Nat.cast_one,Num.add_one]

def incrementMachine : OracleMachine where
  stackCount := 2
  labelCount := 6
  input := 0
  output := 0
  start := 0
  code q := if q = 0 then .pop 0 2 2 1
    else if q = 1 then .push 1 false 0
    else if q = 2 then .push 0 true 3
    else if q = 3 then .pop 1 5 4 4
    else if q = 4 then .push 0 false 3
    else .halt

def incrementConfig (q : Fin 6) (source temporary : BitString) : incrementMachine.Config :=
  ⟨q,Fin.cases source (fun _ => temporary)⟩

lemma increment_pop_nil (g : BitString → ℕ) (temporary : BitString) :
    incrementMachine.step g (incrementConfig 0 [] temporary) =
      some (incrementConfig 2 [] temporary,1) := rfl

lemma increment_pop_false (g : BitString → ℕ) (source temporary : BitString) :
    incrementMachine.step g (incrementConfig 0 (false::source) temporary) =
      some (incrementConfig 2 source temporary,1) := by
  apply congrArg (fun c : incrementMachine.Config => some (c,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

lemma increment_pop_true (g : BitString → ℕ) (source temporary : BitString) :
    incrementMachine.step g (incrementConfig 0 (true::source) temporary) =
      some (incrementConfig 1 source temporary,1) := by
  apply congrArg (fun c : incrementMachine.Config => some (c,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

lemma increment_push_temporary (g : BitString → ℕ) (source temporary : BitString) :
    incrementMachine.step g (incrementConfig 1 source temporary) =
      some (incrementConfig 0 source (false::temporary),1) := by
  apply congrArg (fun c : incrementMachine.Config => some (c,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

lemma increment_push_one (g : BitString → ℕ) (source temporary : BitString) :
    incrementMachine.step g (incrementConfig 2 source temporary) =
      some (incrementConfig 3 (true::source) temporary,1) := by
  apply congrArg (fun c : incrementMachine.Config => some (c,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

lemma increment_restore_nil (g : BitString → ℕ) (source : BitString) :
    incrementMachine.step g (incrementConfig 3 source []) = some (incrementConfig 5 source [],1) := rfl

lemma increment_restore_pop (g : BitString → ℕ) (source temporary : BitString) :
    incrementMachine.step g (incrementConfig 3 source (false::temporary)) =
      some (incrementConfig 4 source temporary,1) := by
  apply congrArg (fun c : incrementMachine.Config => some (c,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

lemma increment_restore_push (g : BitString → ℕ) (source temporary : BitString) :
    incrementMachine.step g (incrementConfig 4 source temporary) =
      some (incrementConfig 3 (false::source) temporary,1) := by
  apply congrArg (fun c : incrementMachine.Config => some (c,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

lemma replicate_cons_append (k : ℕ) (xs : BitString) :
    List.replicate k false ++ false::xs = false::(List.replicate k false++xs) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ,List.cons_append,List.cons.injEq,true_and] using ih

/-- Restore the zeros remembered while traversing a carry. -/
theorem increment_restore (g : BitString → ℕ) (k : ℕ) (source : BitString) :
    incrementMachine.Steps g (incrementConfig 3 source (List.replicate k false))
      (incrementConfig 5 (List.replicate k false++source) []) (2*k+1) := by
  induction k generalizing source with
  | zero => exact OracleMachine.Steps.single (increment_restore_nil g source)
  | succ k ih =>
    have h := (OracleMachine.Steps.single (increment_restore_pop g source (List.replicate k false))).trans
      ((OracleMachine.Steps.single (increment_restore_push g source (List.replicate k false))).trans
        (ih (false::source)))
    convert h using 1
    · simp [List.replicate_succ,replicate_cons_append]
    · omega

/-- Every traversed carry bit costs four bit instructions. -/
theorem increment_steps_aux (g : BitString → ℕ) (source : BitString) (k : ℕ) :
    incrementMachine.Steps g (incrementConfig 0 source (List.replicate k false))
      (incrementConfig 5 (List.replicate k false++incrementBits source) [])
      (4*leadingOnes source+2*k+3) := by
  induction source generalizing k with
  | nil =>
    have h := (OracleMachine.Steps.single (increment_pop_nil g (List.replicate k false))).trans
      ((OracleMachine.Steps.single (increment_push_one g [] (List.replicate k false))).trans
        (increment_restore g k [true]))
    convert h using 1 <;> simp [incrementBits,leadingOnes] <;> omega
  | cons b source ih =>
    cases b
    · have h := (OracleMachine.Steps.single (increment_pop_false g source (List.replicate k false))).trans
        ((OracleMachine.Steps.single (increment_push_one g source (List.replicate k false))).trans
          (increment_restore g k (true::source)))
      convert h using 1 <;> simp [incrementBits,leadingOnes] <;> omega
    · have h := (OracleMachine.Steps.single (increment_pop_true g source (List.replicate k false))).trans
        ((OracleMachine.Steps.single (increment_push_temporary g source (List.replicate k false))).trans
          (by simpa [List.replicate_succ] using ih (k+1)))
      convert h using 1
      · simp [incrementBits,replicate_cons_append]
      · simp [leadingOnes];omega

theorem increment_runs (g : BitString → ℕ) (source : BitString) :
    incrementMachine.Runs g (incrementConfig 0 source [])
      (incrementConfig 5 (incrementBits source) []) (4*leadingOnes source+3) := by
  apply (OracleMachine.runs_iff_steps_halt incrementMachine).mpr
  refine ⟨?_,rfl⟩
  simpa using increment_steps_aux g source 0

lemma increment_initial (source : BitString) :
    incrementMachine.init source = incrementConfig 0 source [] := by
  apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

/-- Operational binary natural addition by one, with no unit-cost integer step. -/
theorem increment_binary_output (g : BitString → ℕ) (n : ℕ) :
    ∃ c : incrementMachine.Config, ∃ t : ℕ,
      incrementMachine.Runs g (incrementMachine.init (Computability.encodeNat n)) c t ∧
      c.stack incrementMachine.output = Computability.encodeNat (n+1) ∧
      t ≤ 4*(Computability.encodeNat n).length+3 := by
  refine ⟨incrementConfig 5 (incrementBits (Computability.encodeNat n)) [],
    4*leadingOnes (Computability.encodeNat n)+3,?_,increment_encodeNat n,?_⟩
  · rw [increment_initial];exact increment_runs g _
  · have := leadingOnes_le_length (Computability.encodeNat n);omega

end HiddenCircuits.Complexity.BitPrograms
