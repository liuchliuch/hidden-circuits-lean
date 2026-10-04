import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength

/-! An actual finite bit-stack comparison of unary values. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

/-- Consume pairs of bits. Empty left means ≤; left present and right empty means >. -/
def unaryLeCore : OracleBlock 2 where
  labelCount := 5
  start := 0
  exit := 4
  code q := if q=0 then .pop 0 2 1 1
    else if q=1 then .pop 1 3 0 0
    else if q=2 then .push 2 true 4
    else if q=3 then .push 2 false 4
    else .halt
  exit_halt := rfl

def leStore (a b out : BitString) : Store 2 := Fin.cases a (Fin.cases b (fun _ => out))

private theorem unaryLe_pop_pair (g : BitString → ℕ) (a b : Bool) (xs ys out : BitString) :
    unaryLeCore.machine.Steps g (unaryLeCore.config (0 : Fin 5) (leStore (a::xs) (b::ys) out))
      (unaryLeCore.config (0 : Fin 5) (leStore xs ys out)) 2 := by
  have h1 : unaryLeCore.machine.step g (unaryLeCore.config (0 : Fin 5) (leStore (a::xs) (b::ys) out)) =
        some (unaryLeCore.config (1 : Fin 5) (leStore xs (b::ys) out),1) := by
    cases a <;> apply congrArg (fun c : unaryLeCore.machine.Config => some (c,1)) <;> apply OracleConfig.ext
    all_goals first | rfl | (intro i; fin_cases i <;> rfl)
  have h2 : unaryLeCore.machine.step g (unaryLeCore.config (1 : Fin 5) (leStore xs (b::ys) out)) =
        some (unaryLeCore.config (0 : Fin 5) (leStore xs ys out),1) := by
    cases b <;> apply congrArg (fun c : unaryLeCore.machine.Config => some (c,1)) <;> apply OracleConfig.ext
    all_goals first | rfl | (intro i; fin_cases i <;> rfl)
  exact (OracleMachine.Steps.single h1).trans (OracleMachine.Steps.single h2)

/-- Correct consuming comparison, with exact bounded operational cost and a
bound on all residual data. Bit values do not affect length comparison. -/
theorem unaryLeCore_executes (g : BitString → ℕ) (xs ys out : BitString) :
    ∃ a b t, unaryLeCore.Executes g (leStore xs ys out)
      (leStore a b (decide (xs.length ≤ ys.length)::out)) t ∧
      t ≤ 2*min xs.length ys.length+3 ∧ a.length+b.length ≤ xs.length+ys.length := by
  induction xs generalizing ys with
  | nil =>
    refine ⟨[],ys,2,?_,by simp,by simp⟩
    have h1 : unaryLeCore.machine.step g (unaryLeCore.config (0 : Fin 5) (leStore [] ys out)) =
        some (unaryLeCore.config (2 : Fin 5) (leStore [] ys out),1) := rfl
    have h2 : unaryLeCore.machine.step g (unaryLeCore.config (2 : Fin 5) (leStore [] ys out)) =
        some (unaryLeCore.config (4 : Fin 5) (leStore [] ys (true::out)),1) := by
      apply congrArg (fun c : unaryLeCore.machine.Config => some (c,1))
      apply OracleConfig.ext
      · rfl
      · intro i; fin_cases i <;> rfl
    exact (OracleMachine.Steps.single h1).trans (OracleMachine.Steps.single h2)
  | cons a xs ih =>
    cases ys with
    | nil =>
      refine ⟨xs,[],3,?_,by simp,by simp⟩
      have h1 : unaryLeCore.machine.step g (unaryLeCore.config (0 : Fin 5) (leStore (a::xs) [] out)) =
          some (unaryLeCore.config (1 : Fin 5) (leStore xs [] out),1) := by
        cases a <;> apply congrArg (fun c : unaryLeCore.machine.Config => some (c,1)) <;> apply OracleConfig.ext
        all_goals first | rfl | (intro i; fin_cases i <;> rfl)
      have h2 : unaryLeCore.machine.step g (unaryLeCore.config (1 : Fin 5) (leStore xs [] out)) =
          some (unaryLeCore.config (3 : Fin 5) (leStore xs [] out),1) := rfl
      have h3 : unaryLeCore.machine.step g (unaryLeCore.config (3 : Fin 5) (leStore xs [] out)) =
          some (unaryLeCore.config (4 : Fin 5) (leStore xs [] (false::out)),1) := by
        apply congrArg (fun c : unaryLeCore.machine.Config => some (c,1))
        apply OracleConfig.ext
        · rfl
        · intro i; fin_cases i <;> rfl
      simpa using (OracleMachine.Steps.single h1).trans
        ((OracleMachine.Steps.single h2).trans (OracleMachine.Steps.single h3))
    | cons b ys =>
      obtain ⟨x,y,t,ht,hb,hsize⟩ := ih ys
      refine ⟨x,y,2+t,?_,?_,?_⟩
      · simpa only [List.length_cons, Nat.add_le_add_iff_right] using (unaryLe_pop_pair g a b xs ys out).trans ht
      · simp only [List.length_cons, min_add_add_right]; omega
      · simp only [List.length_cons]; omega

 theorem unaryLeCore_queryFree : unaryLeCore.QueryFree := by
  intro q i o next
  fin_cases q <;> simp [OracleBlock.machine, unaryLeCore]

/-- Clear both consumed operands, retaining only the comparison bit. -/
noncomputable def unaryLe : OracleBlock 2 := seq unaryLeCore (seq (clear 0) (clear 1))

theorem unaryLe_executes (g : BitString → ℕ) (a b out : BitString) :
    ∃ t, unaryLe.Executes g (leStore a b out)
      (leStore [] [] (decide (a.length ≤ b.length)::out)) t ∧
      t ≤ 3*(a.length+b.length)+9 := by
  obtain ⟨x,y,t,ht,hbound,hsize⟩ := unaryLeCore_executes g a b out
  have hx : (clear (0 : Fin 3)).Executes g (leStore x y (decide (a.length ≤ b.length)::out))
      (leStore [] y (decide (a.length ≤ b.length)::out)) (x.length+1) := by
    convert clear_executes g (0 : Fin 3) (leStore x y (decide (a.length ≤ b.length)::out)) using 1
    funext i; fin_cases i <;> rfl
  have hy : (clear (1 : Fin 3)).Executes g (leStore [] y (decide (a.length ≤ b.length)::out))
      (leStore [] [] (decide (a.length ≤ b.length)::out)) (y.length+1) := by
    convert clear_executes g (1 : Fin 3) (leStore [] y (decide (a.length ≤ b.length)::out)) using 1
    funext i; fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g ht (seq_executes _ _ g hx hy),?_⟩
  have hm : min a.length b.length ≤ a.length+b.length := by omega
  omega

 theorem unaryLe_queryFree : unaryLe.QueryFree :=
  seq_queryFree _ _ unaryLeCore_queryFree (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))

end HiddenCircuits.Approximation.SelfReduction.Runtime
