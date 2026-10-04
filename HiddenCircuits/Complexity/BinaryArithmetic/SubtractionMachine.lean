import HiddenCircuits.Complexity.BinaryArithmetic.Subtraction
import HiddenCircuits.Complexity.TM2BitSimulation
import HiddenCircuits.Complexity.OracleBlocks

namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleMachine

inductive SubState
  | readX (borrow : Bool)
  | readY (borrow : Bool) (x : Option Bool)
  | emit (x y borrow : Bool)
  | finish (borrow : Bool)
  | clear | trim | startReverse | reverse | reversePush (b : Bool) | halt
  deriving DecidableEq, Fintype

noncomputable def subLabel : SubState ≃ Fin (Fintype.card SubState) := Fintype.equivFin _
noncomputable def subCode : SubState → OracleInstr 4 (Fintype.card SubState)
  | .readX c => .pop 0 (subLabel (.readY c none)) (subLabel (.readY c (some false))) (subLabel (.readY c (some true)))
  | .readY c none => .pop 1 (subLabel (.finish c)) (subLabel (.emit false false c)) (subLabel (.emit false true c))
  | .readY c (some a) => .pop 1 (subLabel (.emit a false c)) (subLabel (.emit a false c)) (subLabel (.emit a true c))
  | .emit a b c => .push 2 (sumBit a b c) (subLabel (.readX (borrowBit a b c)))
  | .finish c => .push 3 c (subLabel (if c then .clear else .trim))
  | .clear => .pop 2 (subLabel .halt) (subLabel .clear) (subLabel .clear)
  | .trim => .pop 2 (subLabel .halt) (subLabel .trim) (subLabel .startReverse)
  | .startReverse => .push 0 true (subLabel .reverse)
  | .reverse => .pop 2 (subLabel .halt) (subLabel (.reversePush false)) (subLabel (.reversePush true))
  | .reversePush b => .push 0 b (subLabel .reverse)
  | .halt => .halt

noncomputable abbrev subMachine : OracleMachine where
  stackCount := 4
  labelCount := Fintype.card SubState
  input := 0
  output := 0
  start := subLabel (.readX false)
  code q := subCode (subLabel.symm q)

noncomputable def subConfig (q : SubState) (xs ys tmp flag : BitString) : subMachine.Config :=
  ⟨subLabel q,fun i => if i.val=0 then xs else if i.val=1 then ys else if i.val=2 then tmp else flag⟩

lemma sub_readX_nil (g : BitString → ℕ) (c : Bool) (ys t f : BitString) :
    subMachine.step g (subConfig (.readX c) [] ys t f)=some (subConfig (.readY c none) [] ys t f,1) := by
  simp [OracleMachine.step,subConfig,subMachine,subCode]
lemma sub_readX_cons (g : BitString → ℕ) (c a : Bool) (xs ys t f : BitString) :
    subMachine.step g (subConfig (.readX c) (a::xs) ys t f)=some (subConfig (.readY c (some a)) xs ys t f,1) := by
  cases a <;> simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma sub_readY_nil (g : BitString → ℕ) (c : Bool) (t f : BitString) :
    subMachine.step g (subConfig (.readY c none) [] [] t f)=some (subConfig (.finish c) [] [] t f,1) := by
  simp [OracleMachine.step,subConfig,subMachine,subCode]
lemma sub_readY_some_nil (g : BitString → ℕ) (c a : Bool) (xs t f : BitString) :
    subMachine.step g (subConfig (.readY c (some a)) xs [] t f)=some (subConfig (.emit a false c) xs [] t f,1) := by
  simp [OracleMachine.step,subConfig,subMachine,subCode]
lemma sub_readY_cons (g : BitString → ℕ) (c : Bool) (a : Option Bool) (b : Bool) (xs ys t f : BitString) :
    subMachine.step g (subConfig (.readY c a) xs (b::ys) t f)=some (subConfig (.emit (a.getD false) b c) xs ys t f,1) := by
  cases a <;> cases b <;> simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true,Option.getD]
  all_goals apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma sub_emit (g : BitString → ℕ) (a b c : Bool) (xs ys t f : BitString) :
    subMachine.step g (subConfig (.emit a b c) xs ys t f)=some (subConfig (.readX (borrowBit a b c)) xs ys (sumBit a b c::t) f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

 theorem sub_first_phase (g : BitString → ℕ) (xs ys t f : BitString) (c : Bool) :
    subMachine.Steps g (subConfig (.readX c) xs ys t f)
      (subConfig (.finish (subRaw xs ys c).2) [] [] ((subRaw xs ys c).1.reverse++t) f)
      (3*max xs.length ys.length+2) := by
  induction xs generalizing ys t c with
  | nil =>
    induction ys generalizing t c with
    | nil =>
      simpa [subRaw] using (Steps.single (sub_readX_nil g c [] t f)).trans (Steps.single (sub_readY_nil g c t f))
    | cons b bs ih =>
      have h := (Steps.single (sub_readX_nil g c (b::bs) t f)).trans
        ((Steps.single (sub_readY_cons g c none b [] bs t f)).trans
          ((Steps.single (sub_emit g false b c [] bs t f)).trans
            (ih (sumBit false b c::t) (borrowBit false b c))))
      convert h using 1 <;> simp [subRaw,List.reverse_cons,List.append_assoc] <;> omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have h := (Steps.single (sub_readX_cons g c a as [] t f)).trans
        ((Steps.single (sub_readY_some_nil g c a as t f)).trans
          ((Steps.single (sub_emit g a false c as [] t f)).trans
            (ih [] (sumBit a false c::t) (borrowBit a false c))))
      convert h using 1 <;> simp [subRaw,List.reverse_cons,List.append_assoc] <;> omega
    | cons b bs =>
      have h := (Steps.single (sub_readX_cons g c a as (b::bs) t f)).trans
        ((Steps.single (sub_readY_cons g c (some a) b as bs t f)).trans
          ((Steps.single (sub_emit g a b c as bs t f)).trans
            (ih bs (sumBit a b c::t) (borrowBit a b c))))
      convert h using 1 <;> simp [subRaw,List.reverse_cons,List.append_assoc] <;> omega


lemma sub_finish (g : BitString → ℕ) (c : Bool) (xs ys t f : BitString) :
    subMachine.step g (subConfig (.finish c) xs ys t f)=some (subConfig (if c then .clear else .trim) xs ys t (c::f),1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma sub_clear_nil (g : BitString → ℕ) (xs ys f : BitString) :
    subMachine.step g (subConfig .clear xs ys [] f)=some (subConfig .halt xs ys [] f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma sub_clear_cons (g : BitString → ℕ) (b : Bool) (xs ys t f : BitString) :
    subMachine.step g (subConfig .clear xs ys (b::t) f)=some (subConfig .clear xs ys t f,1) := by
  cases b
  all_goals
    simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
    apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
    · rfl
    · intro i;fin_cases i <;> rfl
lemma sub_trim_nil (g : BitString → ℕ) (xs ys f : BitString) :
    subMachine.step g (subConfig .trim xs ys [] f)=some (subConfig .halt xs ys [] f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma sub_trim_false (g : BitString → ℕ) (xs ys t f : BitString) :
    subMachine.step g (subConfig .trim xs ys (false::t) f)=some (subConfig .trim xs ys t f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma sub_trim_true (g : BitString → ℕ) (xs ys t f : BitString) :
    subMachine.step g (subConfig .trim xs ys (true::t) f)=some (subConfig .startReverse xs ys t f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma sub_start_reverse (g : BitString → ℕ) (xs ys t f : BitString) :
    subMachine.step g (subConfig .startReverse xs ys t f)=some (subConfig .reverse (true::xs) ys t f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma sub_reverse_nil (g : BitString → ℕ) (xs ys f : BitString) :
    subMachine.step g (subConfig .reverse xs ys [] f)=some (subConfig .halt xs ys [] f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma sub_reverse_cons (g : BitString → ℕ) (b : Bool) (xs ys t f : BitString) :
    subMachine.step g (subConfig .reverse xs ys (b::t) f)=some (subConfig (.reversePush b) xs ys t f,1) := by
  cases b
  all_goals
    simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
    apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
    · rfl
    · intro i;fin_cases i <;> rfl
lemma sub_reverse_push (g : BitString → ℕ) (b : Bool) (xs ys t f : BitString) :
    subMachine.step g (subConfig (.reversePush b) xs ys t f)=some (subConfig .reverse (b::xs) ys t f,1) := by
  simp only [OracleMachine.step,subConfig,subMachine,Equiv.symm_apply_apply,subCode,Bool.false_eq_true,ite_false,ite_true]
  apply congrArg (fun d : subMachine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

lemma sub_halt (g : BitString → ℕ) (xs ys t f : BitString) :
    subMachine.step g (subConfig .halt xs ys t f)=none := by
  simp [OracleMachine.step,subConfig,subMachine,subCode]

theorem sub_reverse_phase (g : BitString → ℕ) (xs ys t f : BitString) :
    subMachine.Steps g (subConfig .reverse xs ys t f)
      (subConfig .halt (t.reverse++xs) ys [] f) (2*t.length+1) := by
  induction t generalizing xs with
  | nil => exact Steps.single (sub_reverse_nil g xs ys f)
  | cons b t ih =>
    have h := (Steps.single (sub_reverse_cons g b xs ys t f)).trans
      ((Steps.single (sub_reverse_push g b xs ys t f)).trans (ih (b::xs)))
    convert h using 1 <;> simp [List.reverse_cons,List.append_assoc] <;> omega

def trimCost : BitString → ℕ
  | [] => 1
  | false::t => 1+trimCost t
  | true::t => 2*t.length+3

theorem trimCost_bound (t : BitString) : trimCost t≤2*t.length+1 := by
  induction t with
  | nil => rfl
  | cons b t ih => cases b <;> simp [trimCost] <;> omega

theorem sub_trim_phase (g : BitString → ℕ) (ys t f : BitString) :
    subMachine.Steps g (subConfig .trim [] ys t f)
      (subConfig .halt (normalize t.reverse) ys [] f) (trimCost t) := by
  induction t with
  | nil => exact Steps.single (sub_trim_nil g [] ys f)
  | cons b t ih =>
    cases b with
    | false => simpa [trimCost] using (Steps.single (sub_trim_false g [] ys t f)).trans ih
    | true =>
      have hh := (Steps.single (sub_trim_true g [] ys t f)).trans
        ((Steps.single (sub_start_reverse g [] ys t f)).trans (sub_reverse_phase g [true] ys t f))
      convert hh using 1 <;> simp [trimCost] <;> omega

theorem sub_clear_phase (g : BitString → ℕ) (xs ys t f : BitString) :
    subMachine.Steps g (subConfig .clear xs ys t f) (subConfig .halt xs ys [] f) (t.length+1) := by
  induction t with
  | nil => exact Steps.single (sub_clear_nil g xs ys f)
  | cons b t ih => simpa [Nat.add_comm] using (Steps.single (sub_clear_cons g b xs ys t f)).trans ih


def subCost (xs ys : BitString) : ℕ :=
  3*max xs.length ys.length+3+
    (if (subRaw xs ys false).2 then (subRaw xs ys false).1.length+1
     else trimCost (subRaw xs ys false).1.reverse)

theorem subCost_bound (xs ys : BitString) : subCost xs ys≤5*max xs.length ys.length+4 := by
  have ht := trimCost_bound (subRaw xs ys false).1.reverse
  rw [List.length_reverse,subRaw_length] at ht
  unfold subCost
  split_ifs
  · rw [subRaw_length]; omega
  · omega

theorem sub_steps (g : BitString → ℕ) (xs ys : BitString) :
    subMachine.Steps g (subConfig (.readX false) xs ys [] [])
      (subConfig .halt (subtractBits xs ys) [] [] [(subRaw xs ys false).2]) (subCost xs ys) := by
  have hf := sub_first_phase g xs ys [] [] false
  simp only [List.append_nil] at hf
  cases hb : (subRaw xs ys false).2
  · rw [hb] at hf
    have hh := hf.trans ((Steps.single (sub_finish g false [] [] (subRaw xs ys false).1.reverse [])).trans
      (sub_trim_phase g [] (subRaw xs ys false).1.reverse [false]))
    convert hh using 1 <;> simp [subtractBits,subCost,hb] <;> omega
  · rw [hb] at hf
    have hh := hf.trans ((Steps.single (sub_finish g true [] [] (subRaw xs ys false).1.reverse [])).trans
      (sub_clear_phase g [] [] (subRaw xs ys false).1.reverse [true]))
    convert hh using 1 <;> simp [subtractBits,subCost,hb] <;> omega

theorem sub_runs (g : BitString → ℕ) (xs ys : BitString) :
    subMachine.Runs g (subConfig (.readX false) xs ys [] [])
      (subConfig .halt (subtractBits xs ys) [] [] [(subRaw xs ys false).2]) (subCost xs ys) :=
  (runs_iff_steps_halt _).mpr ⟨sub_steps g xs ys,sub_halt g _ _ _ _⟩

noncomputable def subBlock : OracleBlock 3 where
  labelCount := Fintype.card SubState
  start := subLabel (.readX false)
  exit := subLabel .halt
  code q := subCode (subLabel.symm q)
  exit_halt := by simp [subCode]

def subStore (xs ys t f : BitString) : OracleBlock.Store 3 :=
  fun i => if i.val=0 then xs else if i.val=1 then ys else if i.val=2 then t else f

theorem subBlock_executes (g : BitString → ℕ) (xs ys : BitString) :
    subBlock.Executes g (subStore xs ys [] [])
      (subStore (subtractBits xs ys) [] [] [(subRaw xs ys false).2]) (subCost xs ys) :=
  sub_steps g xs ys

theorem subBlock_queryFree : subBlock.machine.QueryFree := by
  intro q i o next
  change subCode (subLabel.symm q)≠.query i o next
  cases hs : subLabel.symm q with
  | readY c a => cases a <;> simp [subCode]
  | _ => simp [subCode]

theorem subBlock_encode (g : BitString → ℕ) (x y : ℕ) :
    subBlock.Executes g (subStore (Computability.encodeNat x) (Computability.encodeNat y) [] [])
      (subStore (Computability.encodeNat (x-y)) [] [] [decide (x<y)])
      (subCost (Computability.encodeNat x) (Computability.encodeNat y)) := by
  have hh := subBlock_executes g (Computability.encodeNat x) (Computability.encodeNat y)
  rw [subtract_encodeNat] at hh
  have hb : (subRaw (Computability.encodeNat x) (Computability.encodeNat y) false).2=decide (x<y) := by
    apply Bool.eq_iff_iff.mpr
    simpa using subRaw_borrow (Computability.encodeNat x) (Computability.encodeNat y)
  rwa [hb] at hh

end HiddenCircuits.Complexity.BinaryArithmetic
