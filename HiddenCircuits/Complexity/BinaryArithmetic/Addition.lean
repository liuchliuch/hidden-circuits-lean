import HiddenCircuits.Complexity.BinaryArithmetic.Bits

/-! A finite ripple-carry adder. It uses three stacks and a fixed finite
control; all arithmetic on input data is performed by bit pops and pushes. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleMachine

inductive AddState
  | readX (carry : Bool)
  | readY (carry : Bool) (x : Option Bool)
  | emit (x y carry : Bool)
  | finalCarry
  | reverse
  | reversePush (b : Bool)
  | halt
  deriving DecidableEq, Fintype

noncomputable def addLabel : AddState ≃ Fin (Fintype.card AddState) := Fintype.equivFin _

noncomputable def addCode : AddState → OracleInstr 3 (Fintype.card AddState)
  | .readX c => .pop 0 (addLabel (.readY c none))
      (addLabel (.readY c (some false))) (addLabel (.readY c (some true)))
  | .readY c none => .pop 1 (addLabel (if c then .finalCarry else .reverse))
      (addLabel (.emit false false c)) (addLabel (.emit false true c))
  | .readY c (some a) => .pop 1 (addLabel (.emit a false c))
      (addLabel (.emit a false c)) (addLabel (.emit a true c))
  | .emit a b c => .push 2 (sumBit a b c) (addLabel (.readX (carryBit a b c)))
  | .finalCarry => .push 2 true (addLabel .reverse)
  | .reverse => .pop 2 (addLabel .halt) (addLabel (.reversePush false)) (addLabel (.reversePush true))
  | .reversePush b => .push 0 b (addLabel .reverse)
  | .halt => .halt

noncomputable abbrev addMachine : OracleMachine where
  stackCount := 3
  labelCount := Fintype.card AddState
  input := 0
  output := 0
  start := addLabel (.readX false)
  code q := addCode (addLabel.symm q)

noncomputable def addConfig (q : AddState) (xs ys tmp : BitString) : addMachine.Config :=
  ⟨addLabel q,fun i => if i.val = 0 then xs else if i.val = 1 then ys else tmp⟩

@[simp] theorem addMachine_code (q : AddState) : addMachine.code (addLabel q) = addCode q := by
  simp [addMachine]

lemma add_readX_nil (g : BitString → ℕ) (c : Bool) (ys tmp : BitString) :
    addMachine.step g (addConfig (.readX c) [] ys tmp) =
      some (addConfig (.readY c none) [] ys tmp,1) := by
  simp [OracleMachine.step,addConfig,addMachine,addCode]

lemma add_readX_cons (g : BitString → ℕ) (c a : Bool) (xs ys tmp : BitString) :
    addMachine.step g (addConfig (.readX c) (a::xs) ys tmp) =
      some (addConfig (.readY c (some a)) xs ys tmp,1) := by
  cases a <;> simp only [OracleMachine.step,addConfig,addMachine,Equiv.symm_apply_apply,addCode,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : addMachine.Config => some (d,1)); apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma add_readY_nil (g : BitString → ℕ) (c : Bool) (tmp : BitString) :
    addMachine.step g (addConfig (.readY c none) [] [] tmp) =
      some (addConfig (if c then .finalCarry else .reverse) [] [] tmp,1) := by
  simp [OracleMachine.step,addConfig,addMachine,addCode]

lemma add_readY_some_nil (g : BitString → ℕ) (c a : Bool) (xs tmp : BitString) :
    addMachine.step g (addConfig (.readY c (some a)) xs [] tmp) =
      some (addConfig (.emit a false c) xs [] tmp,1) := by
  simp [OracleMachine.step,addConfig,addMachine,addCode]

lemma add_readY_cons (g : BitString → ℕ) (c : Bool) (a : Option Bool) (b : Bool) (xs ys tmp : BitString) :
    addMachine.step g (addConfig (.readY c a) xs (b::ys) tmp) =
      some (addConfig (.emit (a.getD false) b c) xs ys tmp,1) := by
  cases a <;> cases b <;>
    simp only [OracleMachine.step,addConfig,addMachine,Equiv.symm_apply_apply,addCode,Bool.false_eq_true,ite_false,ite_true,Option.getD]
  all_goals apply congrArg (fun d : addMachine.Config => some (d,1)); apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma add_emit (g : BitString → ℕ) (a b c : Bool) (xs ys tmp : BitString) :
    addMachine.step g (addConfig (.emit a b c) xs ys tmp) =
      some (addConfig (.readX (carryBit a b c)) xs ys (sumBit a b c::tmp),1) := by
  simp only [OracleMachine.step,addConfig,addMachine,Equiv.symm_apply_apply,addCode]
  apply congrArg (fun d : addMachine.Config => some (d,1)); apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma add_finalCarry (g : BitString → ℕ) (tmp : BitString) :
    addMachine.step g (addConfig .finalCarry [] [] tmp) =
      some (addConfig .reverse [] [] (true::tmp),1) := by
  simp only [OracleMachine.step,addConfig,addMachine,Equiv.symm_apply_apply,addCode]
  apply congrArg (fun d : addMachine.Config => some (d,1)); apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma add_reverse_nil (g : BitString → ℕ) (xs ys : BitString) :
    addMachine.step g (addConfig .reverse xs ys []) =
      some (addConfig .halt xs ys [],1) := by
  simp [OracleMachine.step,addConfig,addMachine,addCode]

lemma add_reverse_cons (g : BitString → ℕ) (b : Bool) (xs ys tmp : BitString) :
    addMachine.step g (addConfig .reverse xs ys (b::tmp)) =
      some (addConfig (.reversePush b) xs ys tmp,1) := by
  cases b <;> simp only [OracleMachine.step,addConfig,addMachine,Equiv.symm_apply_apply,addCode,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : addMachine.Config => some (d,1)); apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma add_reverse_push (g : BitString → ℕ) (b : Bool) (xs ys tmp : BitString) :
    addMachine.step g (addConfig (.reversePush b) xs ys tmp) =
      some (addConfig .reverse (b::xs) ys tmp,1) := by
  simp only [OracleMachine.step,addConfig,addMachine,Equiv.symm_apply_apply,addCode]
  apply congrArg (fun d : addMachine.Config => some (d,1)); apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma add_halt (g : BitString → ℕ) (xs ys tmp : BitString) :
    addMachine.step g (addConfig .halt xs ys tmp) = none := by
  simp [OracleMachine.step,addConfig,addMachine,addCode]

/-- Cost of the first phase, including the terminal pair of empty-stack tests. -/
def addPhaseCost : BitString → BitString → Bool → ℕ
  | [], [], c => 2+bitVal c
  | a::as, [], c => 3+addPhaseCost as [] (carryBit a false c)
  | [], b::bs, c => 3+addPhaseCost [] bs (carryBit false b c)
  | a::as, b::bs, c => 3+addPhaseCost as bs (carryBit a b c)

theorem addPhaseCost_le (xs ys : BitString) (c : Bool) :
    addPhaseCost xs ys c ≤ 3*max xs.length ys.length+3 := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [addPhaseCost,bitVal]
    | cons b bs ih =>
      have := ih (carryBit false b c)
      simp only [addPhaseCost,List.length_cons,List.length_nil,max_eq_right (Nat.zero_le _)] at *
      omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have := ih [] (carryBit a false c)
      simp only [addPhaseCost,List.length_cons,List.length_nil,max_eq_left (Nat.zero_le _)] at *
      omega
    | cons b bs =>
      have := ih bs (carryBit a b c)
      simp only [addPhaseCost,List.length_cons,max_add_add_right] at *
      omega

/-- Every carry transition is witnessed by the three actual bit instructions. -/
theorem add_first_phase (g : BitString → ℕ) (xs ys tmp : BitString) (c : Bool) :
    addMachine.Steps g (addConfig (.readX c) xs ys tmp)
      (addConfig .reverse [] [] ((addBits xs ys c).reverse++tmp)) (addPhaseCost xs ys c) := by
  induction xs generalizing ys tmp c with
  | nil =>
    induction ys generalizing tmp c with
    | nil =>
      cases c
      · simpa [addBits,addPhaseCost,bitVal] using
          (Steps.single (add_readX_nil g false [] tmp)).trans (Steps.single (add_readY_nil g false tmp))
      · simpa [addBits,addPhaseCost,bitVal] using
          (Steps.single (add_readX_nil g true [] tmp)).trans
            ((Steps.single (add_readY_nil g true tmp)).trans (Steps.single (add_finalCarry g tmp)))
    | cons b bs ih =>
      have h := (Steps.single (add_readX_nil g c (b::bs) tmp)).trans
        ((Steps.single (add_readY_cons g c none b [] bs tmp)).trans
          ((Steps.single (add_emit g false b c [] bs tmp)).trans
            (ih (sumBit false b c::tmp) (carryBit false b c))))
      simpa [addBits,addPhaseCost,List.reverse_cons,List.append_assoc,← Nat.add_assoc] using h
  | cons a as ih =>
    cases ys with
    | nil =>
      have h := (Steps.single (add_readX_cons g c a as [] tmp)).trans
        ((Steps.single (add_readY_some_nil g c a as tmp)).trans
          ((Steps.single (add_emit g a false c as [] tmp)).trans
            (ih [] (sumBit a false c::tmp) (carryBit a false c))))
      simpa [addBits,addPhaseCost,List.reverse_cons,List.append_assoc,← Nat.add_assoc] using h
    | cons b bs =>
      have h := (Steps.single (add_readX_cons g c a as (b::bs) tmp)).trans
        ((Steps.single (add_readY_cons g c (some a) b as bs tmp)).trans
          ((Steps.single (add_emit g a b c as bs tmp)).trans
            (ih bs (sumBit a b c::tmp) (carryBit a b c))))
      simpa [addBits,addPhaseCost,List.reverse_cons,List.append_assoc,← Nat.add_assoc] using h

theorem add_reverse_phase (g : BitString → ℕ) (tmp xs ys : BitString) :
    addMachine.Steps g (addConfig .reverse xs ys tmp)
      (addConfig .halt (tmp.reverse++xs) ys []) (2*tmp.length+1) := by
  induction tmp generalizing xs with
  | nil => exact Steps.single (add_reverse_nil g xs ys)
  | cons b tmp ih =>
    have h := (Steps.single (add_reverse_cons g b xs ys tmp)).trans
      ((Steps.single (add_reverse_push g b xs ys tmp)).trans (ih (b::xs)))
    convert h using 1
    · simp [List.reverse_cons,List.append_assoc]
    · simp; omega

/-- Actual finite-machine addition; both source words are consumed. -/
theorem add_steps (g : BitString → ℕ) (xs ys : BitString) (c : Bool) :
    addMachine.Steps g (addConfig (.readX c) xs ys [])
      (addConfig .halt (addBits xs ys c) [] [])
      (addPhaseCost xs ys c+2*(addBits xs ys c).length+1) := by
  have h := (add_first_phase g xs ys [] c).trans
    (by simpa only [List.append_nil] using add_reverse_phase g (addBits xs ys c).reverse [] [])
  simpa [Nat.add_assoc] using h

theorem add_runs (g : BitString → ℕ) (xs ys : BitString) (c : Bool) :
    addMachine.Runs g (addConfig (.readX c) xs ys [])
      (addConfig .halt (addBits xs ys c) [] [])
      (addPhaseCost xs ys c+2*(addBits xs ys c).length+1) :=
  (runs_iff_steps_halt _).mpr ⟨add_steps g xs ys c,add_halt g _ _ _⟩

/-- Linear bit-operation addition with exact `Computability.encodeNat` output. -/
theorem add_binary_output (g : BitString → ℕ) (m n : ℕ) :
    ∃ (d : addMachine.Config) (t : ℕ),
      addMachine.Runs g
        (addConfig (.readX false) (Computability.encodeNat m) (Computability.encodeNat n) []) d t ∧
      d.stack 0 = Computability.encodeNat (m+n) ∧ d.stack 1 = [] ∧ d.stack 2 = [] ∧
      t ≤ 5*max (Computability.encodeNat m).length (Computability.encodeNat n).length+6 := by
  refine ⟨addConfig .halt (addBits (Computability.encodeNat m) (Computability.encodeNat n) false) [] [],
    _,add_runs g _ _ false,?_,rfl,rfl,?_⟩
  · change addBits _ _ false = _
    simpa [bitVal] using addBits_encodeNat m n false
  · have h₁ := addPhaseCost_le (Computability.encodeNat m) (Computability.encodeNat n) false
    have h₂ := length_addBits (Computability.encodeNat m) (Computability.encodeNat n) false
    omega

end HiddenCircuits.Complexity.BinaryArithmetic
