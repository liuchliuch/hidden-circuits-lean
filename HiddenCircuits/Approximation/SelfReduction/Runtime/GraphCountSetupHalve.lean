import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery
import Mathlib.Data.List.Induction

/-! A literal three-stack unary halver, with an exact even-length decision.
All source bits are consumed; no arithmetic machine instruction is assumed. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup.Halve
open Complexity OracleBlock OracleMachine

abbrev program : OracleBlock 2 where
  labelCount := 6
  start := 0
  exit := 5
  code q := if q=0 then .pop 0 3 1 1 else if q=1 then .pop 0 4 2 2
    else if q=2 then .push 1 true 0 else if q=3 then .push 2 true 5
    else if q=4 then .push 2 false 5 else .halt
  exit_halt := rfl

def store (source quotient flag : BitString) : Store 2 := fun i =>
  if i.val=0 then source else if i.val=1 then quotient else flag

def config (q : Fin 6) (source quotient flag : BitString) : program.machine.Config :=
  ⟨q,store source quotient flag⟩

lemma pop_empty (g : BitString → ℕ) (quotient flag : BitString) :
    program.machine.step g (config 0 [] quotient flag)=some (config 3 [] quotient flag,1) := rfl
lemma pop_first (g : BitString → ℕ) (b : Bool) (source quotient flag : BitString) :
    program.machine.step g (config 0 (b::source) quotient flag)=some (config 1 source quotient flag,1) := by
  cases b <;> apply congrArg (fun s : Store 2 => some ((⟨(1:Fin 6),s⟩ : program.machine.Config),1)) <;>
    funext i <;> fin_cases i <;> rfl
lemma pop_second_empty (g : BitString → ℕ) (quotient flag : BitString) :
    program.machine.step g (config 1 [] quotient flag)=some (config 4 [] quotient flag,1) := rfl
lemma pop_second (g : BitString → ℕ) (b : Bool) (source quotient flag : BitString) :
    program.machine.step g (config 1 (b::source) quotient flag)=some (config 2 source quotient flag,1) := by
  cases b <;> apply congrArg (fun s : Store 2 => some ((⟨(2:Fin 6),s⟩ : program.machine.Config),1)) <;>
    funext i <;> fin_cases i <;> rfl
lemma push_quotient (g : BitString → ℕ) (source quotient flag : BitString) :
    program.machine.step g (config 2 source quotient flag)=some (config 0 source (true::quotient) flag,1) := by
  apply congrArg (fun s : Store 2 => some ((⟨(0:Fin 6),s⟩ : program.machine.Config),1))
  funext i;fin_cases i <;> rfl
lemma push_even (g : BitString → ℕ) (quotient flag : BitString) :
    program.machine.step g (config 3 [] quotient flag)=some (config 5 [] quotient (true::flag),1) := by
  apply congrArg (fun s : Store 2 => some ((⟨(5:Fin 6),s⟩ : program.machine.Config),1))
  funext i;fin_cases i <;> rfl
lemma push_odd (g : BitString → ℕ) (quotient flag : BitString) :
    program.machine.step g (config 4 [] quotient flag)=some (config 5 [] quotient (false::flag),1) := by
  apply congrArg (fun s : Store 2 => some ((⟨(5:Fin 6),s⟩ : program.machine.Config),1))
  funext i;fin_cases i <;> rfl

theorem steps (g : BitString → ℕ) (source quotient flag : BitString) :
    program.machine.Steps g (config 0 source quotient flag)
      (config 5 [] (List.replicate (source.length/2) true++quotient)
        (decide (source.length%2=0)::flag)) (source.length+source.length/2+2) := by
  induction source using List.twoStepInduction generalizing quotient flag with
  | nil =>
    simpa using (Steps.single (pop_empty g quotient flag)).trans (Steps.single (push_even g quotient flag))
  | singleton b =>
    simpa using (Steps.single (pop_first g b [] quotient flag)).trans
      ((Steps.single (pop_second_empty g quotient flag)).trans (Steps.single (push_odd g quotient flag)))
  | cons_cons b c source ih _ =>
    have hh := (Steps.single (pop_first g b (c::source) quotient flag)).trans
      ((Steps.single (pop_second g c source quotient flag)).trans
        ((Steps.single (push_quotient g source quotient flag)).trans (ih (true::quotient) flag)))
    have hd : (b::c::source).length/2=source.length/2+1 := by simp only [List.length_cons];omega
    have hm : (b::c::source).length%2=source.length%2 := by simp only [List.length_cons];omega
    convert hh using 1
    · rw [hd,hm,List.replicate_add,List.append_assoc]
      rfl
    · simp only [List.length_cons] at hd ⊢
      omega

theorem program_executes (g : BitString → ℕ) (source : BitString) :
    program.Executes g (store source [] [])
      (store [] (List.replicate (source.length/2) true) [decide (source.length%2=0)])
      (source.length+source.length/2+2) := by
  simpa using steps g source [] []
lemma program_queryFree : program.QueryFree := by
  intro q i o next;fin_cases q <;> simp [machine,program]

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup.Halve
