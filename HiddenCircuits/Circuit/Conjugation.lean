import HiddenCircuits.Circuit.OneGateWords

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- The two one-bit positions inside an isolated two-bit gate. -/
def firstBit : Placement 2 1 := ⟨0,1,rfl⟩
def secondBit : Placement 2 1 := ⟨1,0,rfl⟩

def scaleFirst : Matrix (Fin 4) (Fin 4) ℚ := Matrix.diagonal ![2,2,1,1]
def scaleSecond : Matrix (Fin 4) (Fin 4) ℚ := Matrix.diagonal ![2,1,2,1]
def swapFirst : Matrix (Fin 4) (Fin 4) ℚ := !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0]
def swapSecond : Matrix (Fin 4) (Fin 4) ℚ := !![0,1,0,0;1,0,0,0;0,0,0,1;0,0,1,0]

/-- These are genuine individually placed available one-bit gates. -/
theorem first_scale_basis : (firstBit.lift OneGate.scale.logical).submatrix twoBitEquiv twoBitEquiv=scaleFirst := by
  decide +kernel
 theorem second_scale_basis : (secondBit.lift OneGate.scale.logical).submatrix twoBitEquiv twoBitEquiv=scaleSecond := by
  decide +kernel
 theorem first_swap_basis : (firstBit.lift OneGate.swap.logical).submatrix twoBitEquiv twoBitEquiv=swapFirst := by
  decide +kernel
 theorem second_swap_basis : (secondBit.lift OneGate.swap.logical).submatrix twoBitEquiv twoBitEquiv=swapSecond := by
  decide +kernel

 theorem scaleFirst_pow (u : ℕ) : scaleFirst^u=Matrix.diagonal ![(2:ℚ)^u,2^u,1,1] := by
  rw [scaleFirst,Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> simp
 theorem scaleSecond_pow (u : ℕ) : scaleSecond^u=Matrix.diagonal ![(2:ℚ)^u,1,2^u,1] := by
  rw [scaleSecond,Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> simp

/-- Left conjugation uses only2u copies of Q and one explicit scalar. -/
theorem conjugating_inverse_word (u : ℕ) :
    (((2:ℚ)^u)⁻¹)^2 • (scaleFirst^u * scaleSecond^u)=conjugatingDiagonal (((2:ℚ)^u)⁻¹) := by
  rw [scaleFirst_pow,scaleSecond_pow]
  ext i j
  have hq : (2:ℚ)^u≠0 := by positivity
  fin_cases i <;> fin_cases j <;>
    simp [conjugatingDiagonal,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul] <;>
    field_simp

theorem swapFirst_diagonal (q : ℚ) :
    swapFirst * Matrix.diagonal ![q,q,1,1] * swapFirst = Matrix.diagonal ![1,1,q,q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapFirst,Matrix.mul_diagonal,Matrix.mul_apply,Matrix.vecMul, dotProduct,Matrix.diagonal_apply,Fin.sum_univ_succ]

theorem swapSecond_diagonal (q : ℚ) :
    swapSecond * Matrix.diagonal ![q,1,q,1] * swapSecond = Matrix.diagonal ![1,q,1,q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapSecond,Matrix.mul_diagonal,Matrix.mul_apply,Matrix.vecMul, dotProduct,Matrix.diagonal_apply,Fin.sum_univ_succ]

/-- Right conjugation uses two XQ^uX operations, one on each wire. -/
theorem conjugating_word (u : ℕ) :
    (swapFirst * scaleFirst^u * swapFirst) * (swapSecond * scaleSecond^u * swapSecond) =
      conjugatingDiagonal ((2:ℚ)^u) := by
  rw [scaleFirst_pow,scaleSecond_pow,swapFirst_diagonal,swapSecond_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugatingDiagonal,Matrix.diagonal_mul,Matrix.diagonal_apply,pow_two]

/-- A sample of the shared G(q) family is an explicit available-gate product of length4u+5. -/
theorem sampledG_available_product (u : ℕ) :
    evaluateMatrix ((2:ℚ)^u) GPolynomial = (((2:ℚ)^u)⁻¹)^2 •
      (scaleFirst^u * scaleSecond^u * G *
        swapFirst * scaleFirst^u * swapFirst * swapSecond * scaleSecond^u * swapSecond) := by
  rw [GPolynomial_conjugate _ (by positivity),← conjugating_inverse_word u,← conjugating_word u]
  simp only [smul_mul_assoc,Matrix.mul_assoc]

end HiddenCircuits.Circuit
