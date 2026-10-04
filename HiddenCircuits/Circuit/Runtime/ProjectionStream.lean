import HiddenCircuits.Circuit.Runtime.ProjectionStreamLoop

namespace HiddenCircuits.Circuit.Runtime.ProjectionStream
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock Polynomial
noncomputable def program : OracleBlock 10 := seq prepare projectionLoop
noncomputable def time : Polynomial ℕ :=
  100*(X+1)^2+(2*X^2+2)*(X*(3000*(4*X+1)+2)+9*X+10)+3

theorem program_executes (oracle : BitString → ℕ) (n : ℕ) (out exponent : BitString) :
    ∃t, program.Executes oracle (store n 0 0 0 out exponent)
      (store n 0 0 0 ((encodeBitList ((globalProjectionWord n).map letterBits)).reverse++out)
        (List.replicate (6*n*globalProjectionExponent n) true++exponent)) t ∧ t≤time.eval n := by
  obtain ⟨a,ha,hab⟩ := prepare_executes oracle n out exponent
  obtain ⟨b,hb,hbb⟩ := projectionLoop_executes oracle (globalProjectionExponent n) n out exponent
  rw [projectionStream_eq] at hb
  refine ⟨a+b+2,seq_executes _ _ oracle ha hb,?_⟩
  have he : globalProjectionExponent n≤2*n^2+2 := by
    unfold globalProjectionExponent
    have := Nat.mul_le_mul_left (2*n) (Nat.sub_le n 1)
    nlinarith
  have hm := Nat.mul_le_mul_right (scanTime n+2) he
  simp only [time,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one,eval_X]
  unfold scanTime at hbb hm
  nlinarith

theorem program_queryFree : program.QueryFree := seq_queryFree _ _ prepare_queryFree projectionLoop_queryFree
end HiddenCircuits.Circuit.Runtime.ProjectionStream
