import HiddenCircuits.Circuit.Placement

namespace HiddenCircuits.Circuit
open Polynomial
open scoped Kronecker
noncomputable section

/-- The exact rational two-bit gate certified by the literal eight-track computation. -/
def G : Matrix (Fin 4) (Fin 4) ℚ := !![-2,2,-7/2,-6;0,-3,0,-2;0,0,2,-4;0,0,0,1]
def delta : Matrix (Fin 4) (Fin 4) ℚ := Matrix.diagonal ![-2,-3,2,1]

/-- Shared conjugation parameter, retaining every actual off-diagonal coefficient. -/
def GPolynomial : Matrix (Fin 4) (Fin 4) ℚ[X] :=
  !![-2,2*X,Polynomial.C (-7/2)*X,-6*X^2;0,-3,0,-2*X;0,0,2,-4*X;0,0,0,1]

 theorem GPolynomial_degree : PolynomialMatrixDegree GPolynomial 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [GPolynomial]

 theorem GPolynomial_zero : evaluateMatrix 0 GPolynomial=delta := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [GPolynomial,delta,evaluateMatrix,Matrix.diagonal_apply]

 theorem GPolynomial_one : evaluateMatrix 1 GPolynomial=G := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [GPolynomial,G,evaluateMatrix]

/-- K(q)⊗K(q), in the fixed two-bit basis. -/
def conjugatingDiagonal (q : ℚ) : Matrix (Fin 4) (Fin 4) ℚ := Matrix.diagonal ![1,q,q,q^2]

/-- Exact implementation of the polynomial family by conjugating the fixed G gate. -/
theorem GPolynomial_conjugate (q : ℚ) (hq : q≠0) :
    evaluateMatrix q GPolynomial = conjugatingDiagonal q⁻¹ * G * conjugatingDiagonal q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GPolynomial,G,evaluateMatrix,conjugatingDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal] <;>
    field_simp <;> ring

/-- Lift the literal4×4 polynomial into the actual two-bit tuple space. -/
def logicalGPolynomial : Matrix (CodeBits 2) (CodeBits 2) ℚ[X] :=
  GPolynomial.submatrix twoBitEquiv.symm twoBitEquiv.symm

def logicalDelta : Matrix (CodeBits 2) (CodeBits 2) ℚ :=
  delta.submatrix twoBitEquiv.symm twoBitEquiv.symm

 theorem logicalGPolynomial_degree : PolynomialMatrixDegree logicalGPolynomial 2 :=
  fun x y => GPolynomial_degree _ _

@[simp] theorem logicalGPolynomial_zero : evaluateMatrix 0 logicalGPolynomial=logicalDelta := by
  ext x y
  exact congrFun (congrFun GPolynomial_zero (twoBitEquiv.symm x)) (twoBitEquiv.symm y)

end
end HiddenCircuits.Circuit
