import HiddenCircuits.Complexity.BinaryArithmetic.SignedMultiplication
import HiddenCircuits.Complexity.BinaryArithmetic.SignedDivision

/-! Uniform polynomial witnesses and terminating finite-machine executions
for signed arithmetic. Operand lengths include their actual sign bits. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock OracleMachine

noncomputable def integerMultiplicationTime : Polynomial ℕ := 50*(Polynomial.X+1)^3
noncomputable def integerDivisionTime : Polynomial ℕ := 100*(Polynomial.X+1)^2

lemma multiplication_bound_polynomial (L K N : ℕ) (hL : L≤N) (hK : K≤N) :
    13+2*L+L*(5*(L*(K+2))+10*K+22) ≤ integerMultiplicationTime.eval N := by
  calc
    _ ≤ 13+2*N+N*(5*(N*(N+2))+10*N+22) := by gcongr
    _ ≤ _ := by
      simp only [integerMultiplicationTime,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
        Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
      ring_nf
      omega

lemma division_bound_polynomial (L K N : ℕ) (hL : L≤N) (hK : K≤N) :
    L*(25*K+54)+13 ≤ integerDivisionTime.eval N := by
  calc
    _ ≤ N*(25*N+54)+13 := by gcongr
    _ ≤ _ := by
      simp only [integerDivisionTime,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
        Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
      ring_nf
      omega

theorem signed_multiply_polynomial (g : BitString → ℕ) (a b : ℤ) :
    ∃ t : ℕ, signedMultiplicationBlock.Executes g
      (mulStore (signedBits a) (signedBits b) [] [] [] [])
      (mulStore [] (Computability.encodeNat b.natAbs) (signedBits (a*b)) [] [] []) t ∧
      t ≤ integerMultiplicationTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨t,ht,hb⟩ := signed_multiply_binary_output g a b
  refine ⟨t,ht,hb.trans (multiplication_bound_polynomial _ _ _ ?_ ?_)⟩ <;>
    simp only [signedBits,List.length_cons] <;> omega

theorem signed_exact_divide_polynomial (g : BitString → ℕ) (a b : ℤ) (hb : b≠0) (hdiv : b ∣ a) :
    ∃ t : ℕ, signedDivisionBlock.Executes g
      (divStore (signedBits a) (signedBits b) [] [] [] [] [] [] [])
      (divStore [] (Computability.encodeNat b.natAbs) [] (signedBits (a/b)) [] [] [] [] []) t ∧
      t ≤ integerDivisionTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨t,ht,hbound⟩ := signed_exact_divide_binary_output g a b hb hdiv
  refine ⟨t,ht,hbound.trans (division_bound_polynomial _ _ _ ?_ ?_)⟩ <;>
    simp only [signedBits,List.length_cons] <;> omega

/-- A complete terminating execution, including the actual designated halt. -/
theorem signed_multiply_runs (g : BitString → ℕ) (a b : ℤ) :
    ∃ (c : signedMultiplicationBlock.machine.Config) (t : ℕ),
      signedMultiplicationBlock.machine.Runs g
        (signedMultiplicationBlock.config signedMultiplicationBlock.start
          (mulStore (signedBits a) (signedBits b) [] [] [] [])) c t ∧
      c.stack (2 : Fin 6) = signedBits (a*b) ∧
      t ≤ integerMultiplicationTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨t,ht,hbound⟩ := signed_multiply_polynomial g a b
  refine ⟨signedMultiplicationBlock.config signedMultiplicationBlock.exit
    (mulStore [] (Computability.encodeNat b.natAbs) (signedBits (a*b)) [] [] []),t,?_,rfl,hbound⟩
  apply (runs_iff_steps_halt _).mpr
  refine ⟨ht,?_⟩
  simp [OracleMachine.step,machine,config,signedMultiplicationBlock.exit_halt]

/-- Complete finite execution of exact signed division; the sign operation,
all long-division iterations, and the terminating halt have been verified. -/
theorem signed_exact_divide_runs (g : BitString → ℕ) (a b : ℤ) (hb : b≠0) (hdiv : b ∣ a) :
    ∃ (c : signedDivisionBlock.machine.Config) (t : ℕ),
      signedDivisionBlock.machine.Runs g
        (signedDivisionBlock.config signedDivisionBlock.start
          (divStore (signedBits a) (signedBits b) [] [] [] [] [] [] [])) c t ∧
      c.stack (3 : Fin 9) = signedBits (a/b) ∧
      t ≤ integerDivisionTime.eval ((signedBits a).length+(signedBits b).length) := by
  obtain ⟨t,ht,hbound⟩ := signed_exact_divide_polynomial g a b hb hdiv
  refine ⟨signedDivisionBlock.config signedDivisionBlock.exit
    (divStore [] (Computability.encodeNat b.natAbs) [] (signedBits (a/b)) [] [] [] [] []),t,?_,rfl,hbound⟩
  apply (runs_iff_steps_halt _).mpr
  refine ⟨ht,?_⟩
  simp [OracleMachine.step,machine,config,signedDivisionBlock.exit_halt]

end HiddenCircuits.Complexity.BinaryArithmetic
