import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Actual consuming comparison of two unary clocks or two bitstring lengths. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.LengthLess
open Complexity
open OracleBlock

def lengthLessBlock : OracleBlock 2 where
  labelCount := 6
  start := 0
  exit := 5
  code q :=
    if q=0 then .pop 0 1 2 2
    else if q=1 then .pop 1 4 3 3
    else if q=2 then .pop 1 4 0 0
    else if q=3 then .push 2 true 5
    else if q=4 then .push 2 false 5
    else .halt
  exit_halt := rfl

def lengthLessStore (a b out : BitString) : Store 2 := Fin.cases a (Fin.cases b (fun _ => out))

private theorem lengthLess_pop_both (g : BitString → ℕ) (a b : Bool) (xs ys out : BitString) :
    lengthLessBlock.machine.Steps g
      (lengthLessBlock.config (0 : Fin 6) (lengthLessStore (a::xs) (b::ys) out))
      (lengthLessBlock.config (0 : Fin 6) (lengthLessStore xs ys out)) 2 := by
  have h₁ : lengthLessBlock.machine.step g
      (lengthLessBlock.config (0 : Fin 6) (lengthLessStore (a::xs) (b::ys) out)) =
      some (lengthLessBlock.config (2 : Fin 6) (lengthLessStore xs (b::ys) out),1) := by
    cases a <;> apply congrArg (fun c : lengthLessBlock.machine.Config => some (c,1)) <;>
      apply OracleConfig.ext
    all_goals first | rfl | (intro i;fin_cases i <;> rfl)
  have h₂ : lengthLessBlock.machine.step g
      (lengthLessBlock.config (2 : Fin 6) (lengthLessStore xs (b::ys) out)) =
      some (lengthLessBlock.config (0 : Fin 6) (lengthLessStore xs ys out),1) := by
    cases b <;> apply congrArg (fun c : lengthLessBlock.machine.Config => some (c,1)) <;>
      apply OracleConfig.ext
    all_goals first | rfl | (intro i;fin_cases i <;> rfl)
  exact (OracleMachine.Steps.single h₁).trans (OracleMachine.Steps.single h₂)

private theorem lengthLess_finish (g : BitString → ℕ) (b : Bool) (xs ys out : BitString) :
    lengthLessBlock.machine.step g
      (lengthLessBlock.config (if b then (3:Fin 6) else (4:Fin 6)) (lengthLessStore xs ys out))=
      some (lengthLessBlock.config (5:Fin 6) (lengthLessStore xs ys (b::out)),1) := by
  cases b <;> apply congrArg (fun c : lengthLessBlock.machine.Config => some (c,1)) <;>
    apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

/-- The output bit is the exact strict length comparison. All malformed or unequal lengths terminate too. -/
theorem lengthLess_executes (g : BitString → ℕ) (xs ys out : BitString) :
    ∃ a b cost, lengthLessBlock.Executes g (lengthLessStore xs ys out)
      (lengthLessStore a b (decide (xs.length<ys.length)::out)) cost ∧
      cost ≤ 2*min xs.length ys.length+3 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨[],[],3,?_,by simp⟩
      have h₁ : lengthLessBlock.machine.step g
          (lengthLessBlock.config (0:Fin 6) (lengthLessStore [] [] out))=
          some (lengthLessBlock.config (1:Fin 6) (lengthLessStore [] [] out),1) := rfl
      have h₂ : lengthLessBlock.machine.step g
          (lengthLessBlock.config (1:Fin 6) (lengthLessStore [] [] out))=
          some (lengthLessBlock.config (4:Fin 6) (lengthLessStore [] [] out),1) := rfl
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthLess_finish g false [] [] out)))
    | cons b ys =>
      refine ⟨[],ys,3,?_,by simp⟩
      have h₁ : lengthLessBlock.machine.step g
          (lengthLessBlock.config (0 : Fin 6) (lengthLessStore [] (b::ys) out))=
          some (lengthLessBlock.config (1 : Fin 6) (lengthLessStore [] (b::ys) out),1) := rfl
      have h₂ : lengthLessBlock.machine.step g
          (lengthLessBlock.config (1 : Fin 6) (lengthLessStore [] (b::ys) out))=
          some (lengthLessBlock.config (3 : Fin 6) (lengthLessStore [] ys out),1) := by
        cases b <;> apply congrArg (fun c : lengthLessBlock.machine.Config => some (c,1)) <;>
          apply OracleConfig.ext
        all_goals first | rfl | (intro i;fin_cases i <;> rfl)
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthLess_finish g true [] ys out)))
  | cons a xs ih =>
    cases ys with
    | nil =>
      refine ⟨xs,[],3,?_,by simp⟩
      have h₁ : lengthLessBlock.machine.step g
          (lengthLessBlock.config (0 : Fin 6) (lengthLessStore (a::xs) [] out))=
          some (lengthLessBlock.config (2 : Fin 6) (lengthLessStore xs [] out),1) := by
        cases a <;> apply congrArg (fun c : lengthLessBlock.machine.Config => some (c,1)) <;>
          apply OracleConfig.ext
        all_goals first | rfl | (intro i;fin_cases i <;> rfl)
      have h₂ : lengthLessBlock.machine.step g
          (lengthLessBlock.config (2:Fin 6) (lengthLessStore xs [] out))=
          some (lengthLessBlock.config (4:Fin 6) (lengthLessStore xs [] out),1) := rfl
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthLess_finish g false xs [] out)))
    | cons b ys =>
      obtain ⟨x,y,c,hc,hbound⟩ := ih ys
      refine ⟨x,y,2+c,?_,?_⟩
      · simpa only [List.length_cons,Nat.add_lt_add_iff_right] using
          (lengthLess_pop_both g a b xs ys out).trans hc
      · simp only [List.length_cons,min_add_add_right]
        omega

 theorem lengthLess_queryFree : lengthLessBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine,lengthLessBlock]

end HiddenCircuits.Approximation.SamplerRuntime.LengthLess
