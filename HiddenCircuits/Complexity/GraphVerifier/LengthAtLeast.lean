import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Actual consuming comparison of two unary clocks or two bitstring lengths. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def lengthAtLeastBlock : OracleBlock 2 where
  labelCount := 6
  start := 0
  exit := 5
  code q :=
    if q=0 then .pop 0 1 2 2
    else if q=1 then .pop 1 3 4 4
    else if q=2 then .pop 1 3 0 0
    else if q=3 then .push 2 true 5
    else if q=4 then .push 2 false 5
    else .halt
  exit_halt := rfl

def lengthAtLeastStore (a b out : BitString) : Store 2 := Fin.cases a (Fin.cases b (fun _ => out))

private theorem lengthAtLeast_pop_both (g : BitString → ℕ) (a b : Bool) (xs ys out : BitString) :
    lengthAtLeastBlock.machine.Steps g
      (lengthAtLeastBlock.config (0 : Fin 6) (lengthAtLeastStore (a::xs) (b::ys) out))
      (lengthAtLeastBlock.config (0 : Fin 6) (lengthAtLeastStore xs ys out)) 2 := by
  have h₁ : lengthAtLeastBlock.machine.step g
      (lengthAtLeastBlock.config (0 : Fin 6) (lengthAtLeastStore (a::xs) (b::ys) out)) =
      some (lengthAtLeastBlock.config (2 : Fin 6) (lengthAtLeastStore xs (b::ys) out),1) := by
    cases a <;> apply congrArg (fun c : lengthAtLeastBlock.machine.Config => some (c,1)) <;>
      apply OracleConfig.ext
    all_goals first | rfl | (intro i;fin_cases i <;> rfl)
  have h₂ : lengthAtLeastBlock.machine.step g
      (lengthAtLeastBlock.config (2 : Fin 6) (lengthAtLeastStore xs (b::ys) out)) =
      some (lengthAtLeastBlock.config (0 : Fin 6) (lengthAtLeastStore xs ys out),1) := by
    cases b <;> apply congrArg (fun c : lengthAtLeastBlock.machine.Config => some (c,1)) <;>
      apply OracleConfig.ext
    all_goals first | rfl | (intro i;fin_cases i <;> rfl)
  exact (OracleMachine.Steps.single h₁).trans (OracleMachine.Steps.single h₂)

private theorem lengthAtLeast_finish (g : BitString → ℕ) (b : Bool) (xs ys out : BitString) :
    lengthAtLeastBlock.machine.step g
      (lengthAtLeastBlock.config (if b then (3:Fin 6) else (4:Fin 6)) (lengthAtLeastStore xs ys out))=
      some (lengthAtLeastBlock.config (5:Fin 6) (lengthAtLeastStore xs ys (b::out)),1) := by
  cases b <;> apply congrArg (fun c : lengthAtLeastBlock.machine.Config => some (c,1)) <;>
    apply OracleConfig.ext
  all_goals first | rfl | (intro i;fin_cases i <;> rfl)

/-- The output bit is the exact non-strict length comparison. All malformed or unequal lengths terminate too. -/
theorem lengthAtLeast_executes (g : BitString → ℕ) (xs ys out : BitString) :
    ∃ a b cost, lengthAtLeastBlock.Executes g (lengthAtLeastStore xs ys out)
      (lengthAtLeastStore a b (decide (ys.length≤xs.length)::out)) cost ∧
      cost ≤ 2*min xs.length ys.length+3 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨[],[],3,?_,by simp⟩
      have h₁ : lengthAtLeastBlock.machine.step g
          (lengthAtLeastBlock.config (0:Fin 6) (lengthAtLeastStore [] [] out))=
          some (lengthAtLeastBlock.config (1:Fin 6) (lengthAtLeastStore [] [] out),1) := rfl
      have h₂ : lengthAtLeastBlock.machine.step g
          (lengthAtLeastBlock.config (1:Fin 6) (lengthAtLeastStore [] [] out))=
          some (lengthAtLeastBlock.config (3:Fin 6) (lengthAtLeastStore [] [] out),1) := rfl
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthAtLeast_finish g true [] [] out)))
    | cons b ys =>
      refine ⟨[],ys,3,?_,by simp⟩
      have h₁ : lengthAtLeastBlock.machine.step g
          (lengthAtLeastBlock.config (0 : Fin 6) (lengthAtLeastStore [] (b::ys) out))=
          some (lengthAtLeastBlock.config (1 : Fin 6) (lengthAtLeastStore [] (b::ys) out),1) := rfl
      have h₂ : lengthAtLeastBlock.machine.step g
          (lengthAtLeastBlock.config (1 : Fin 6) (lengthAtLeastStore [] (b::ys) out))=
          some (lengthAtLeastBlock.config (4 : Fin 6) (lengthAtLeastStore [] ys out),1) := by
        cases b <;> apply congrArg (fun c : lengthAtLeastBlock.machine.Config => some (c,1)) <;>
          apply OracleConfig.ext
        all_goals first | rfl | (intro i;fin_cases i <;> rfl)
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthAtLeast_finish g false [] ys out)))
  | cons a xs ih =>
    cases ys with
    | nil =>
      refine ⟨xs,[],3,?_,by simp⟩
      have h₁ : lengthAtLeastBlock.machine.step g
          (lengthAtLeastBlock.config (0 : Fin 6) (lengthAtLeastStore (a::xs) [] out))=
          some (lengthAtLeastBlock.config (2 : Fin 6) (lengthAtLeastStore xs [] out),1) := by
        cases a <;> apply congrArg (fun c : lengthAtLeastBlock.machine.Config => some (c,1)) <;>
          apply OracleConfig.ext
        all_goals first | rfl | (intro i;fin_cases i <;> rfl)
      have h₂ : lengthAtLeastBlock.machine.step g
          (lengthAtLeastBlock.config (2:Fin 6) (lengthAtLeastStore xs [] out))=
          some (lengthAtLeastBlock.config (3:Fin 6) (lengthAtLeastStore xs [] out),1) := rfl
      exact (OracleMachine.Steps.single h₁).trans
        ((OracleMachine.Steps.single h₂).trans (OracleMachine.Steps.single (lengthAtLeast_finish g true xs [] out)))
    | cons b ys =>
      obtain ⟨x,y,c,hc,hbound⟩ := ih ys
      refine ⟨x,y,2+c,?_,?_⟩
      · simpa only [List.length_cons,Nat.add_le_add_iff_right] using
          (lengthAtLeast_pop_both g a b xs ys out).trans hc
      · simp only [List.length_cons,min_add_add_right]
        omega

 theorem lengthAtLeast_queryFree : lengthAtLeastBlock.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine,lengthAtLeastBlock]

end HiddenCircuits.Complexity.GraphVerifier.Runtime
