import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
import HiddenCircuits.Complexity.DeterminantRuntime.Trace
import HiddenCircuits.Complexity.DeterminantRuntime.Coefficient
import HiddenCircuits.Complexity.DeterminantRuntime.RoundLayout

/-! Framed operational stages of the exact integer determinant round. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Round
open OracleBlock BinaryArithmetic
variable {n : ℕ}

noncomputable def productStage : OracleBlock 30 := MatrixProduct.on productPorts
noncomputable def traceStage : OracleBlock 30 := Trace.on tracePorts
noncomputable def coefficientStage : OracleBlock 30 := Coefficient.on coefficientPorts

theorem productStage_executes (g : BitString → ℕ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (c : BitString) (k clock : ℕ) :
    ∃ t, productStage.Executes g (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) c k clock)
      (state n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) c k clock
        (encodeBitList (matrixWords (A*B))) [] [] []) t ∧ t ≤ MatrixProduct.timePolynomial.eval (MatrixProduct.inputSize A B) := by
  obtain ⟨t,ht,hb⟩ := MatrixProduct.on_executes productPorts g A B
    (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) c k clock)
    (by funext q; fin_cases q <;> rfl)
  have he : Function.update (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) c k clock)
      (productPorts 7) (encodeBitList (matrixWords (A*B))) =
      state n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) c k clock
        (encodeBitList (matrixWords (A*B))) [] [] [] := by funext q; fin_cases q <;> rfl
  rw [he] at ht
  exact ⟨t,ht,hb⟩

theorem traceStage_executes (g : BitString → ℕ) (C : Matrix (Fin n) (Fin n) ℤ)
    (a b c : BitString) (k clock : ℕ) :
    ∃ t, traceStage.Executes g (state n a b c k clock (encodeBitList (matrixWords C)) [] [] [])
      (state n a b c k clock (encodeBitList (matrixWords C)) (signedBits C.trace) [] []) t ∧
      t ≤ Trace.timePolynomial.eval (n+(encodeBitList (matrixWords C)).length+1) := by
  obtain ⟨t,ht,hb⟩ := Trace.on_executes tracePorts g C
    (state n a b c k clock (encodeBitList (matrixWords C)) [] [] [])
    (by funext q; fin_cases q <;> rfl)
  have he : Function.update (state n a b c k clock (encodeBitList (matrixWords C)) [] [] [])
      (tracePorts 2) (signedBits C.trace) =
      state n a b c k clock (encodeBitList (matrixWords C)) (signedBits C.trace) [] [] := by
    funext q; fin_cases q <;> rfl
  rw [he] at ht
  exact ⟨t,ht,hb⟩

theorem coefficientStage_executes (g : BitString → ℕ) (n : ℕ) (a b c product : BitString)
    (k clock : ℕ) (trace : ℤ) (hdiv : ((k+1 : ℕ) : ℤ) ∣ -trace) :
    ∃ t, coefficientStage.Executes g (state n a b c k clock product (signedBits trace) [] [])
      (state n a b c k clock product (signedBits trace) (signedBits ((-trace)/(k+1 : ℕ))) []) t ∧
      t ≤ Coefficient.timePolynomial.eval (k+(signedBits trace).length+1) := by
  obtain ⟨t,ht,hb⟩ := Coefficient.on_executes coefficientPorts g k trace hdiv
    (state n a b c k clock product (signedBits trace) [] [])
    (by funext q; fin_cases q <;> rfl)
  have he : Function.update (state n a b c k clock product (signedBits trace) [] [])
      (coefficientPorts 2) (signedBits ((-trace)/(k+1 : ℕ))) =
      state n a b c k clock product (signedBits trace) (signedBits ((-trace)/(k+1 : ℕ))) [] := by
    funext q; fin_cases q <;> rfl
  rw [he] at ht
  exact ⟨t,ht,hb⟩

end HiddenCircuits.Complexity.DeterminantRuntime.Round
