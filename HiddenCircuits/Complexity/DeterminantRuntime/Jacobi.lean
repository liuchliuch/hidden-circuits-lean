import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-! Formal polynomial Jacobi
identity. The permutation formula occurs only in this mathematical proof. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem derivative_det (M : Matrix ι ι R[X]) :
    derivative M.det = ∑ j, (M.updateCol j (fun i => derivative (M i j))).det := by
  rw [Matrix.det_apply']
  simp only [derivative_sum, derivative_intCast_mul, derivative_prod_finset,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  rw [Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact (Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)).symm

theorem derivative_charmatrix (A : Matrix ι ι R) (i j : ι) :
    derivative (Matrix.charmatrix A i j) = (Pi.single j (1 : R[X]) : ι → R[X]) i := by
  by_cases h : i = j
  · subst i; simp
  · simp [h]

theorem adjugate_diagonal_eq_updateCol_det (M : Matrix ι ι R) (i : ι) :
    M.adjugate i i = (M.updateCol i (Pi.single i 1)).det := by
  have h := Matrix.adjugate_apply M.transpose i i
  rw [← Matrix.adjugate_transpose, Matrix.transpose_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose] at h
  exact h

theorem derivative_charpoly (A : Matrix ι ι R) :
    derivative A.charpoly = (Matrix.charmatrix A).adjugate.trace := by
  rw [Matrix.charpoly, derivative_det, Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diag_apply, adjugate_diagonal_eq_updateCol_det]
  congr 2
  funext i
  exact derivative_charmatrix A i j

end HiddenCircuits.Complexity.DeterminantRuntime
