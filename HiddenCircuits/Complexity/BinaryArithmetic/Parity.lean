import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! A finite unary parity program, used for interpolation coefficient signs. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleMachine OracleBlock

def parityBit : ℕ → Bool
  | 0 => false
  | n+1 => !(parityBit n)

@[simp] theorem signedNat_parity (n : ℕ) : signedNat (parityBit n) 1=(-1 : ℤ)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parityBit,pow_succ,←ih]
    cases parityBit n <;> simp [signedNat]

theorem finishSigned_parity (n m : ℕ) :
    finishSigned (parityBit n) (Computability.encodeNat m)=signedBits ((-1 : ℤ)^n*(m : ℤ)) := by
  rw [finishSigned_encode,←signedNat_parity]
  congr 1
  cases parityBit n <;> simp [signedNat]

abbrev parityBlock : OracleBlock 1 where
  labelCount := 5
  start := 0
  exit := 4
  code q := if q=0 then .pop 0 2 1 1 else if q=1 then .pop 0 3 0 0
    else if q=2 then .push 1 false 4 else if q=3 then .push 1 true 4 else .halt
  exit_halt := rfl

def parityStore (source output : BitString) : Store 1 := fun i => if i.val=0 then source else output

def parityConfig (q : Fin 5) (source output : BitString) : parityBlock.machine.Config := ⟨q,parityStore source output⟩

lemma parity_pop_nil (g : BitString → ℕ) (c : Bool) (output : BitString) :
    parityBlock.machine.step g (parityConfig (if c then 1 else 0) [] output)=
      some (parityConfig (if c then 3 else 2) [] output,1) := by
  cases c <;> rfl

lemma parity_pop_cons (g : BitString → ℕ) (c b : Bool) (source output : BitString) :
    parityBlock.machine.step g (parityConfig (if c then 1 else 0) (b::source) output)=
      some (parityConfig (if !c then 1 else 0) source output,1) := by
  cases c <;> cases b <;> apply congrArg (fun d : parityBlock.machine.Config => some (d,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

lemma parity_push (g : BitString → ℕ) (c : Bool) (source output : BitString) :
    parityBlock.machine.step g (parityConfig (if c then 3 else 2) source output)=
      some (parityConfig 4 source (c::output),1) := by
  cases c <;> apply congrArg (fun d : parityBlock.machine.Config => some (d,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i; fin_cases i <;> rfl)

theorem parity_steps (g : BitString → ℕ) (source output : BitString) (c : Bool) :
    parityBlock.machine.Steps g (parityConfig (if c then 1 else 0) source output)
      (parityConfig 4 [] (xor c (parityBit source.length)::output)) (source.length+2) := by
  induction source generalizing c with
  | nil =>
    have h := (Steps.single (parity_pop_nil g c output)).trans (Steps.single (parity_push g c [] output))
    cases c <;> simpa [parityBit] using h
  | cons b source ih =>
    have h := (Steps.single (parity_pop_cons g c b source output)).trans (ih (!c))
    have he : xor (!c) (parityBit source.length)=xor c (!(parityBit source.length)) := by
      cases c <;> cases parityBit source.length <;> rfl
    simpa [List.length_cons,parityBit,he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Parity consumes only the unary clock and pushes one literal sign bit. -/
theorem parityBlock_executes (g : BitString → ℕ) (source output : BitString) :
    parityBlock.Executes g (parityStore source output)
      (parityStore [] (parityBit source.length::output)) (source.length+2) := by
  simpa using parity_steps g source output false

lemma parityBlock_queryFree : parityBlock.QueryFree := by
  intro q i o next; fin_cases q <;> simp [machine,parityBlock]

noncomputable def finishFrom {k : ℕ} (flag output : Fin (k+1)) : OracleBlock k :=
  branchPop flag skip (finishOn output false) (finishOn output true)

theorem finishFrom_executes {k : ℕ} (g : BitString → ℕ) (flag output : Fin (k+1))
    (hne : flag≠output) (s : Store k) (b : Bool) (hb : s flag=[b]) :
    (finishFrom flag output).Executes g s
      (Function.update (Function.update s flag []) output (finishSigned b (s output))) (finishCost (s output)+2) := by
  have ho : Function.update s flag [] output=s output := Function.update_of_ne hne.symm _ _
  have hf := finishOn_executes g output b (Function.update s flag [])
  rw [ho] at hf
  cases b
  · exact branchPop_false _ _ _ _ g hb hf
  · exact branchPop_true _ _ _ _ g hb hf

lemma finishFrom_queryFree {k : ℕ} (flag output : Fin (k+1)) : (finishFrom flag output).QueryFree :=
  branchPop_queryFree _ _ _ _ skip_queryFree (finishOn_queryFree _ _) (finishOn_queryFree _ _)

end HiddenCircuits.Complexity.BinaryArithmetic
