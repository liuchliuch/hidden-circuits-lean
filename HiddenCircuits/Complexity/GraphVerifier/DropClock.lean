import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Actual bounded prefix deletion for false-padding checks and flat matrix traversal. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock
variable {k : ℕ}

def popDrop (stack : Fin (k+1)) : OracleBlock k where
  labelCount := 2
  start := 0
  exit := 1
  code q := if q=0 then .pop stack 1 1 1 else .halt
  exit_halt := rfl

 theorem popDrop_executes (stack : Fin (k+1)) (g : BitString → ℕ) (s : Store k) :
    (popDrop stack).Executes g s (Function.update s stack (s stack).tail) 1 := by
  apply OracleMachine.Steps.single
  change (popDrop stack).machine.step g ⟨(0:Fin 2),s⟩=some (⟨(1:Fin 2),Function.update s stack (s stack).tail⟩,1)
  cases hs : s stack with
  | nil =>
    have he : Function.update s stack ([]:BitString)=s := by
      funext i
      by_cases hi : i=stack
      · subst i
        rw [Function.update_self,hs]
      · exact Function.update_of_ne hi _ _
    simp [OracleMachine.step,OracleBlock.machine,popDrop,hs,he]
  | cons b bs => cases b <;> simp [OracleMachine.step,OracleBlock.machine,popDrop,hs]

 theorem popDrop_queryFree (stack : Fin (k+1)) : (popDrop stack).QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine,popDrop]

noncomputable def dropClockBlock : OracleBlock 1 := whilePop 1 (popDrop 0) (popDrop 0)

def dropClockStore (data clock : BitString) : Store 1 := Fin.cases data (fun _ => clock)

 theorem dropClock_execution (g : BitString → ℕ) (data clock : BitString) :
    dropClockBlock.Executes g (dropClockStore data clock)
      (dropClockStore (data.drop clock.length) []) (3*clock.length+1) := by
  apply whilePop_executes
  induction clock generalizing data with
  | nil =>
    simpa using (WhileExecution.empty (stack:=(1:Fin 2)) (B:=popDrop 0) (C:=popDrop 0)
      (g:=g) (dropClockStore data []) rfl)
  | cons b clock ih =>
    have he : Function.update (dropClockStore data (b::clock)) (1:Fin 2) clock=dropClockStore data clock := by
      funext i;fin_cases i <;> rfl
    have hp : (popDrop (0:Fin 2)).Executes g (Function.update (dropClockStore data (b::clock)) 1 clock)
        (dropClockStore data.tail clock) 1 := by
      rw [he]
      have hh := popDrop_executes (0:Fin 2) g (dropClockStore data clock)
      have hout : Function.update (dropClockStore data clock) (0:Fin 2) data.tail=dropClockStore data.tail clock := by
        funext i;fin_cases i <;> rfl
      change (popDrop (0:Fin 2)).Executes g (dropClockStore data clock)
        (Function.update (dropClockStore data clock) 0 data.tail) 1 at hh
      rwa [hout] at hh
    have hi := ih data.tail
    have hdrop : data.tail.drop clock.length=data.drop (clock.length+1) := by
      cases data <;> simp
    cases b with
    | false =>
      have hh := WhileExecution.zero (stack:=(1:Fin 2)) rfl hp hi
      convert hh using 1 <;> simp only [List.length_cons,hdrop,Nat.mul_add,Nat.mul_one] <;> omega
    | true =>
      have hh := WhileExecution.one (stack:=(1:Fin 2)) rfl hp hi
      convert hh using 1 <;> simp only [List.length_cons,hdrop,Nat.mul_add,Nat.mul_one] <;> omega

 theorem dropClock_queryFree : dropClockBlock.QueryFree :=
  whilePop_queryFree _ _ _ (popDrop_queryFree _) (popDrop_queryFree _)

end HiddenCircuits.Complexity.GraphVerifier.Runtime
