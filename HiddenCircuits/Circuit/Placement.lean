import HiddenCircuits.LogicalConcat
import HiddenCircuits.PairedInterpolation

namespace HiddenCircuits.Circuit
open scoped Kronecker BigOperators
open Polynomial

/-- An explicit interval of d adjacent logical wires in an n-bit circuit. -/
structure Placement (n d : ℕ) where
  before : ℕ
  after : ℕ
  size : before+(d+after)=n

/-- Consecutive logical tuple splitting, independent of any physical transfer assumption. -/
def blockEquiv (b r c : ℕ) : CodeBits b × (CodeBits r × CodeBits c) ≃ CodeBits (b+(r+c)) :=
  (Equiv.prodCongr (Equiv.refl _) (codeConcatEquiv r c)).trans (codeConcatEquiv b (r+c))

def Placement.equiv {n d : ℕ} (p : Placement n d) :
    CodeBits p.before × (CodeBits d × CodeBits p.after) ≃ CodeBits n :=
  (blockEquiv p.before d p.after).trans (Equiv.cast (congrArg CodeBits p.size))

/-- The ordinary logical tensor-local gate on the explicitly specified adjacent wires. -/
def Placement.lift {R : Type*} [Semiring R] {n d : ℕ} (p : Placement n d)
    (A : Matrix (CodeBits d) (CodeBits d) R) : Matrix (CodeBits n) (CodeBits n) R :=
  (1 ⊗ₖ (A ⊗ₖ 1)).submatrix p.equiv.symm p.equiv.symm

 theorem Placement.lift_mul {R : Type*} [CommSemiring R] {n d : ℕ} (p : Placement n d)
    (A B : Matrix (CodeBits d) (CodeBits d) R) : p.lift (A*B)=p.lift A * p.lift B := by
  unfold lift
  rw [← Matrix.submatrix_mul _ _ _ _ _ p.equiv.symm.bijective,
    ← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,one_mul,one_mul]

@[simp] theorem Placement.lift_one {R : Type*} [Semiring R] {n d : ℕ} (p : Placement n d) :
    p.lift (1 : Matrix (CodeBits d) (CodeBits d) R)=1 := by
  unfold lift
  rw [Matrix.one_kronecker_one,Matrix.one_kronecker_one]
  ext x y
  simp [Matrix.one_apply,p.equiv.symm.injective.eq_iff]

 theorem evaluate_lift {n d : ℕ} (p : Placement n d)
    (A : Matrix (CodeBits d) (CodeBits d) ℚ[X]) (t : ℚ) :
    evaluateMatrix t (p.lift A)=p.lift (evaluateMatrix t A) := by
  ext x y
  simp only [evaluateMatrix,Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    Matrix.one_apply,Polynomial.eval_mul]
  split_ifs <;> simp

 theorem constant_lift {n d : ℕ} (p : Placement n d)
    (A : Matrix (CodeBits d) (CodeBits d) ℚ) :
    constantMatrix (p.lift A)=p.lift (constantMatrix A) := by
  ext x y
  simp only [constantMatrix,Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,
    Matrix.one_apply,map_mul]
  split_ifs <;> simp

 theorem Placement.lift_degree {n d b : ℕ} (p : Placement n d)
    (A : Matrix (CodeBits d) (CodeBits d) ℚ[X]) (hA : PolynomialMatrixDegree A b) :
    PolynomialMatrixDegree (p.lift A) b := by
  intro x y
  simp only [Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply]
  split_ifs <;> simpa using hA (p.equiv.symm x).2.1 (p.equiv.symm y).2.1

/-- Standard one-bit basis order0,1. -/
def oneBitEquiv : Fin 2 ≃ CodeBits 1 where
  toFun i := (i,PUnit.unit)
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := by cases x with | mk a b => cases b; rfl

/-- Standard two-bit basis order00,01,10,11. -/
def twoBitEquiv : Fin 4 ≃ CodeBits 2 :=
  (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm.trans
    (Equiv.prodCongr (Equiv.refl _) oneBitEquiv)

end HiddenCircuits.Circuit
