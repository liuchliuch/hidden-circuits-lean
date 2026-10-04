import HiddenCircuits.Complexity.GraphVerifier.UnpairProgram
import HiddenCircuits.Complexity.OracleBlocks
import HiddenCircuits.Complexity.TM2BitSimulation

/-! Read-only unary length and all-true header validation using real bit instructions. -/
namespace HiddenCircuits.Complexity.GraphVerifier.UnaryHeader
open OracleMachine

inductive State
  | read (valid : Bool) | save (valid bit : Bool) | tick (valid bit : Bool)
  | finish (valid : Bool) | reverse | pushBack (bit : Bool) | halt
  deriving DecidableEq, Fintype
noncomputable def label : State ≃ Fin (Fintype.card State) := Fintype.equivFin _
noncomputable def code : State → OracleInstr 4 (Fintype.card State)
  | .read c => .pop 0 (label (.finish c)) (label (.save c false)) (label (.save c true))
  | .save c b => .push 2 b (label (.tick c b))
  | .tick c b => .push 1 true (label (.read (c && b)))
  | .finish c => .push 3 c (label .reverse)
  | .reverse => .pop 2 (label .halt) (label (.pushBack false)) (label (.pushBack true))
  | .pushBack b => .push 0 b (label .reverse)
  | .halt => .halt
noncomputable abbrev machine : OracleMachine where
  stackCount := 4
  labelCount := Fintype.card State
  input := 0
  output := 0
  start := label (.read true)
  code q := code (label.symm q)

def store (xs unary tmp flag : BitString) : OracleBlock.Store 3 :=
  fun i => if i.val=0 then xs else if i.val=1 then unary else if i.val=2 then tmp else flag
noncomputable def config (q : State) (xs unary tmp flag : BitString) : machine.Config :=
  ⟨label q,store xs unary tmp flag⟩

lemma read_nil (g : BitString → ℕ) (c : Bool) (u t f : BitString) :
    machine.step g (config (.read c) [] u t f)=some (config (.finish c) [] u t f,1) := by
  simp [OracleMachine.step,config,store,machine,code]
lemma read_cons (g : BitString → ℕ) (c b : Bool) (xs u t f : BitString) :
    machine.step g (config (.read c) (b::xs) u t f)=some (config (.save c b) xs u t f,1) := by
  cases b <;> simp only [OracleMachine.step,config,store,machine,Equiv.symm_apply_apply,code,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : machine.Config => some (d,1));apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma save_step (g : BitString → ℕ) (c b : Bool) (xs u t f : BitString) :
    machine.step g (config (.save c b) xs u t f)=some (config (.tick c b) xs u (b::t) f,1) := by
  simp only [OracleMachine.step,config,store,machine,Equiv.symm_apply_apply,code]
  apply congrArg (fun d : machine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma tick_step (g : BitString → ℕ) (c b : Bool) (xs u t f : BitString) :
    machine.step g (config (.tick c b) xs u t f)=some (config (.read (c && b)) xs (true::u) t f,1) := by
  simp only [OracleMachine.step,config,store,machine,Equiv.symm_apply_apply,code]
  apply congrArg (fun d : machine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl
lemma finish_step (g : BitString → ℕ) (c : Bool) (xs u t f : BitString) :
    machine.step g (config (.finish c) xs u t f)=some (config .reverse xs u t (c::f),1) := by
  simp only [OracleMachine.step,config,store,machine,Equiv.symm_apply_apply,code]
  apply congrArg (fun d : machine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

private theorem replicate_push (n : ℕ) (u : BitString) :
    true::(List.replicate n true++u)=List.replicate n true++true::u := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons true) ih

theorem scan_steps (g : BitString → ℕ) (c : Bool) (xs u t f : BitString) :
    machine.Steps g (config (.read c) xs u t f)
      (config .reverse [] (List.replicate xs.length true++u) (xs.reverse++t) ((c && xs.all id)::f))
      (3*xs.length+2) := by
  induction xs generalizing c u t with
  | nil => simpa using (Steps.single (read_nil g c u t f)).trans (Steps.single (finish_step g c [] u t f))
  | cons b xs ih =>
    have hh := (Steps.single (read_cons g c b xs u t f)).trans
      ((Steps.single (save_step g c b xs u t f)).trans
        ((Steps.single (tick_step g c b xs u (b::t) f)).trans
          (ih (c && b) (true::u) (b::t))))
    convert hh using 1 <;> simp [List.reverse_cons,List.append_assoc,List.replicate_succ,Bool.and_assoc,replicate_push] <;> omega

lemma reverse_nil (g : BitString → ℕ) (xs u f : BitString) :
    machine.step g (config .reverse xs u [] f)=some (config .halt xs u [] f,1) := by
  simp [OracleMachine.step,config,store,machine,code]
lemma reverse_cons (g : BitString → ℕ) (b : Bool) (xs u t f : BitString) :
    machine.step g (config .reverse xs u (b::t) f)=some (config (.pushBack b) xs u t f,1) := by
  cases b <;> simp only [OracleMachine.step,config,store,machine,Equiv.symm_apply_apply,code,Bool.false_eq_true,ite_false,ite_true]
  all_goals apply congrArg (fun d : machine.Config => some (d,1));apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma pushBack_step (g : BitString → ℕ) (b : Bool) (xs u t f : BitString) :
    machine.step g (config (.pushBack b) xs u t f)=some (config .reverse (b::xs) u t f,1) := by
  simp only [OracleMachine.step,config,store,machine,Equiv.symm_apply_apply,code]
  apply congrArg (fun d : machine.Config => some (d,1));apply OracleConfig.ext
  · rfl
  · intro i;fin_cases i <;> rfl

theorem restore_steps (g : BitString → ℕ) (xs u t f : BitString) :
    machine.Steps g (config .reverse xs u t f) (config .halt (t.reverse++xs) u [] f) (2*t.length+1) := by
  induction t generalizing xs with
  | nil => exact Steps.single (reverse_nil g xs u f)
  | cons b t ih =>
    have hh := (Steps.single (reverse_cons g b xs u t f)).trans
      ((Steps.single (pushBack_step g b xs u t f)).trans (ih (b::xs)))
    convert hh using 1 <;> simp [List.reverse_cons,List.append_assoc] <;> omega

theorem header_steps (g : BitString → ℕ) (xs : BitString) :
    machine.Steps g (config (.read true) xs [] [] [])
      (config .halt xs (List.replicate xs.length true) [] [xs.all id]) (5*xs.length+3) := by
  have hh := (scan_steps g true xs [] [] []).trans
    (by simpa using restore_steps g [] (List.replicate xs.length true) xs.reverse [xs.all id])
  convert hh using 1 <;> try simp
  all_goals omega

noncomputable def block : OracleBlock 3 where
  labelCount := Fintype.card State
  start := label (.read true)
  exit := label .halt
  code q := code (label.symm q)
  exit_halt := by simp [code]

theorem block_executes (g : BitString → ℕ) (xs : BitString) :
    block.Executes g (store xs [] [] [])
      (store xs (List.replicate xs.length true) [] [xs.all id]) (5*xs.length+3) :=
  header_steps g xs

theorem block_queryFree : block.machine.QueryFree := by
  intro q i o next
  change code (label.symm q)≠.query i o next
  cases label.symm q <;> simp [code]

end HiddenCircuits.Complexity.GraphVerifier.UnaryHeader
