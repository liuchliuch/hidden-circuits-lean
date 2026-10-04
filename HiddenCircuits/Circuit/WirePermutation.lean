import HiddenCircuits.Circuit.BitAssignments

namespace HiddenCircuits.Circuit
open scoped BigOperators

/-- Relabel actual source assignments by the permutation of their current wire positions. -/
def assignmentPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun f := fun i => f (σ.symm i)
  invFun f := fun i => f (σ i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

/-- The same explicit coordinate relabeling on the canonical logical bit-string type. -/
def wirePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : CodeBits n ≃ CodeBits n :=
  (assignmentEquiv n).trans ((assignmentPermutation σ).trans (assignmentEquiv n).symm)

 theorem wirePermutation_bits {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : CodeBits n) (i : Fin n) :
    bitsToAssignment n (wirePermutation σ x) i=bitsToAssignment n x (σ.symm i) := by
  change (assignmentEquiv n) ((assignmentEquiv n).symm ((assignmentPermutation σ) ((assignmentEquiv n) x))) i=_
  rw [Equiv.apply_symm_apply]
  rfl

 theorem wirePermutation_one {n : ℕ} (x : CodeBits n) : wirePermutation (1 : Equiv.Perm (Fin n)) x=x := by
  apply (assignmentEquiv n).injective
  funext i
  exact wirePermutation_bits 1 x i

 theorem wirePermutation_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (x : CodeBits n) :
    wirePermutation (σ*τ) x=wirePermutation σ (wirePermutation τ x) := by
  apply (assignmentEquiv n).injective
  funext i
  change bitsToAssignment n _ i=bitsToAssignment n _ i
  rw [wirePermutation_bits,wirePermutation_bits,wirePermutation_bits]
  rfl

 theorem wirePermutation_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : wirePermutation σ (zeroBits n)=zeroBits n := by
  apply (assignmentEquiv n).injective
  funext i
  change bitsToAssignment n _ i=bitsToAssignment n _ i
  simp only [wirePermutation_bits,zeroBits_assignment]

/-- The actual row-vector permutation matrix, with all coefficients zero or one. -/
def wireMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (CodeBits n) (CodeBits n) ℚ :=
  fun x y => if y=wirePermutation σ x then 1 else 0

@[simp] theorem wireMatrix_one (n : ℕ) : wireMatrix (1 : Equiv.Perm (Fin n))=1 := by
  ext x y
  simp [wireMatrix,wirePermutation_one,Matrix.one_apply,eq_comm]

/-- Row-vector order composes the actual wire relabelings from left to right. -/
theorem wireMatrix_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    wireMatrix σ * wireMatrix τ = wireMatrix (τ*σ) := by
  ext x y
  rw [Matrix.mul_apply,Finset.sum_eq_single (wirePermutation σ x)]
  · simp [wireMatrix,wirePermutation_mul]
  · intro z _ hz
    simp [wireMatrix,hz]
  · simp

@[simp] theorem wireMatrix_inverse {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    wireMatrix σ * wireMatrix σ⁻¹=1 := by rw [wireMatrix_mul,inv_mul_cancel,wireMatrix_one]

/-- Moving a diagonal constraint back through a routed wire permutation updates its vertex labels exactly. -/
theorem wireMatrix_diagonal {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : CodeBits n → ℚ) :
    wireMatrix σ * Matrix.diagonal f =
      Matrix.diagonal (fun x => f (wirePermutation σ x)) * wireMatrix σ := by
  ext x y
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [wireMatrix]
  by_cases h:y=wirePermutation σ x
  · simp [h]
  · simp [h]

/-- A route and its inverse conjugate a local constraint to the exact relabeled diagonal. -/
theorem wireMatrix_conjugate_diagonal {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : CodeBits n → ℚ) :
    wireMatrix σ * Matrix.diagonal f * wireMatrix σ⁻¹ =
      Matrix.diagonal (fun x => f (wirePermutation σ x)) := by
  rw [wireMatrix_diagonal,Matrix.mul_assoc,wireMatrix_inverse,mul_one]

end HiddenCircuits.Circuit
