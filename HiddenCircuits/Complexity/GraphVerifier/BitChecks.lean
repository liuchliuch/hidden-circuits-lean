import HiddenCircuits.Complexity.OracleBlocks
import HiddenCircuits.Complexity.TM2BitSimulation

/-! Constant-bit word checks with fully consumed input and a singleton Boolean output. -/
namespace HiddenCircuits.Complexity.GraphVerifier.BitChecks
open OracleMachine

def machine (expected : Bool) : OracleMachine where
  stackCount := 1
  labelCount := 5
  input := 0
  output := 0
  start := 0
  code q := if q=0 then .pop 0 2 (if expected then 1 else 0) (if expected then 0 else 1)
    else if q=1 then .pop 0 3 1 1
    else if q=2 then .push 0 true 4
    else if q=3 then .push 0 false 4
    else .halt

def config (e : Bool) (q : Fin 5) (xs : BitString) : (machine e).Config := ⟨q,fun _ => xs⟩

def readLabel (c : Bool) : Fin 5 := if c then 0 else 1
def finishLabel (c : Bool) : Fin 5 := if c then 2 else 3

lemma pop_nil (g : BitString → ℕ) (e c : Bool) :
    (machine e).step g (config e (readLabel c) [])=some (config e (finishLabel c) [],1) := by
  cases e <;> cases c <;> rfl
lemma pop_cons (g : BitString → ℕ) (e c b : Bool) (xs : BitString) :
    (machine e).step g (config e (readLabel c) (b::xs))=
      some (config e (readLabel (c && (b==e))) xs,1) := by
  cases e <;> cases c <;> cases b <;>
    apply congrArg (fun d : (machine _).Config => some (d,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)
lemma push_result (g : BitString → ℕ) (e c : Bool) :
    (machine e).step g (config e (finishLabel c) [])=some (config e 4 [c],1) := by
  cases e <;> cases c <;> apply congrArg (fun d : (machine _).Config => some (d,1)) <;> apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

theorem check_steps (g : BitString → ℕ) (e c : Bool) (xs : BitString) :
    (machine e).Steps g (config e (readLabel c) xs)
      (config e 4 [c && xs.all (fun b => b==e)]) (xs.length+2) := by
  induction xs generalizing c with
  | nil => simpa using (Steps.single (pop_nil g e c)).trans (Steps.single (push_result g e c))
  | cons b xs ih =>
    have hh := (Steps.single (pop_cons g e c b xs)).trans (ih (c && (b==e)))
    convert hh using 1 <;> simp [Bool.and_assoc] <;> omega

def block (e : Bool) : OracleBlock 0 where
  labelCount := 5
  start := 0
  exit := 4
  code := (machine e).code
  exit_halt := rfl

theorem block_executes (g : BitString → ℕ) (e : Bool) (xs : BitString) :
    (block e).Executes g (fun _ => xs) (fun _ => [xs.all (fun b => b==e)]) (xs.length+2) := by
  simpa using check_steps g e true xs

theorem block_queryFree (e : Bool) : (block e).machine.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [block,OracleBlock.machine,machine]

end HiddenCircuits.Complexity.GraphVerifier.BitChecks
