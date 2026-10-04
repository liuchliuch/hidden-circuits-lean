import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Actual consuming comparison of two unary clocks or two bitstring lengths. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def lengthCompareBlock : OracleBlock 2 where
  labelCount := 6
  start := 0
  exit := 5
  code q :=
    if q=0 then .pop 0 1 2 2
    else if q=1 then .pop 1 3 4 4
    else if q=2 then .pop 1 4 0 0
    else if q=3 then .push 2 true 5
    else if q=4 then .push 2 false 5
    else .halt
  exit_halt := rfl

def lengthCompareStore (a b out : BitString) : Store 2 := Fin.cases a (Fin.cases b (fun _ => out))

private theorem lengthCompare_pop_both (g : BitString → ℕ) (a b : Bool) (xs ys out : BitString) :
    lengthCompareBlock.machine.Steps g
      (lengthCompareBlock.config (0 : Fin 6) (lengthCompareStore (a::xs) (b::ys) out))
      (lengthCompareBlock.config (0 : Fin 6) (lengthCompareStore xs ys out)) 2 := by
  have h₁ : lengthCompareBlock.machine.step g
      (lengthCompareBlock.config (0 : Fin 6) (lengthCompareStore (a::xs) (b::ys) out)) =
      some (lengthCompareBlock.config (2 : Fin 6) (lengthCompareStore xs (b::ys) out),1) := by
    cases a <;> apply congrArg (fun c : lengthCompareBlock.machine.Config => some (c,1)) <;>
      apply OracleConfig.ext
    all_goals first | rfl | (intro i;fin_cases i <;> rfl)
  have h₂ : lengthCompareBlock.machine.step g
      (lengthCompareBlock.config (2 : Fin 6) (lengthCompareStore xs (b::ys) out)) =
      some (lengthCompareBlock.config (0 : Fin 6) (lengthCompareStore xs ys out),1) := by
    cases b <;> apply congrArg (fun c : lengthCompareBlock.machine.Config => some (c,1)) <;>
      apply OracleConfig.ext
    all_goals first | rfl | (intro i;fin_cases i <;> rfl)
  exact (OracleMachine.Steps.single h₁).trans (OracleMachine.Steps.single h₂)

private theorem lengthCompare_finish (g : BitString → ℕ) (b : Bool) (xs ys out : BitString) :
    lengthCompareBlock.machine.step g
      (lengthCompareBlock.config (if b then (3:Fin 6) else (4:Fin 6)) (lengthCompareStore xs ys out))=
      some (lengthCompareBlock.config (5:Fin 6) (lengthCompareStore xs ys (b::out)),1) := by
  cases b <;> apply congrArg (fun c : lengthCompareBlock.machine.Config => some (c,1)) <;>
    apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

/-- The output bit is the exact length equality. All malformed or unequal lengths terminate too. -/
theorem lengthCompare_executes (g : BitString → ℕ) (xs ys out : BitString) :
    ∃ a b cost, lengthCompareBlock.Executes g (lengthCompareStore xs ys out)
      (lengthCompareStore a b (decide (xs.length=ys.length)::out)) cost ∧
      cost ≤ 2*min xs.length ys.length+3 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨[],[],3,?_,by simp⟩
      have h₁ : lengthCompareBlock.machine.step g
          (lengthCompareBlock.config (0:Fin 6) (lengthCompareStore [] [] out))=
          some (lengthCompareBlock.config (1:Fin 6) (lengthCompareStore [] [] out),1) := rfl
      have h₂ : lengthCompareBlock.machine.step g
          (lengthCompareBlock.config (1:Fin 6) (lengthCompareStore [] [] out))=
          some (lengthCompareBlock.config (3:Fin 6) (lengthCompareStore [] [] out),1) := rfl
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthCompare_finish g true [] [] out)))
    | cons b ys =>
      refine ⟨[],ys,3,?_,by simp⟩
      have h₁ : lengthCompareBlock.machine.step g
          (lengthCompareBlock.config (0 : Fin 6) (lengthCompareStore [] (b::ys) out))=
          some (lengthCompareBlock.config (1 : Fin 6) (lengthCompareStore [] (b::ys) out),1) := rfl
      have h₂ : lengthCompareBlock.machine.step g
          (lengthCompareBlock.config (1 : Fin 6) (lengthCompareStore [] (b::ys) out))=
          some (lengthCompareBlock.config (4 : Fin 6) (lengthCompareStore [] ys out),1) := by
        cases b <;> apply congrArg (fun c : lengthCompareBlock.machine.Config => some (c,1)) <;>
          apply OracleConfig.ext
        all_goals first | rfl | (intro i;fin_cases i <;> rfl)
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthCompare_finish g false [] ys out)))
  | cons a xs ih =>
    cases ys with
    | nil =>
      refine ⟨xs,[],3,?_,by simp⟩
      have h₁ : lengthCompareBlock.machine.step g
          (lengthCompareBlock.config (0 : Fin 6) (lengthCompareStore (a::xs) [] out))=
          some (lengthCompareBlock.config (2 : Fin 6) (lengthCompareStore xs [] out),1) := by
        cases a <;> apply congrArg (fun c : lengthCompareBlock.machine.Config => some (c,1)) <;>
          apply OracleConfig.ext
        all_goals first | rfl | (intro i;fin_cases i <;> rfl)
      have h₂ : lengthCompareBlock.machine.step g
          (lengthCompareBlock.config (2:Fin 6) (lengthCompareStore xs [] out))=
          some (lengthCompareBlock.config (4:Fin 6) (lengthCompareStore xs [] out),1) := rfl
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthCompare_finish g false xs [] out)))
    | cons b ys =>
      obtain ⟨x,y,c,hc,hbound⟩ := ih ys
      refine ⟨x,y,2+c,?_,?_⟩
      · simpa only [List.length_cons,Nat.add_left_inj] using
          (lengthCompare_pop_both g a b xs ys out).trans hc
      · simp only [List.length_cons,min_add_add_right]
        omega

 theorem lengthCompare_queryFree : lengthCompareBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine,lengthCompareBlock]

end HiddenCircuits.Complexity.GraphVerifier.Runtime
