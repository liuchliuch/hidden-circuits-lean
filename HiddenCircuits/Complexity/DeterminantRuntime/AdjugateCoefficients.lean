import HiddenCircuits.Complexity.DeterminantRuntime.Jacobi

/-! Integer adjugate coefficient identities supporting exact
Faddeev–LeVerrier divisions. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open Matrix Polynomial Finset
variable {n : ℕ}

noncomputable def adjCoeff (A : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  (matPolyEquiv (Matrix.charmatrix A).adjugate).coeff d

@[simp] theorem adjCoeff_apply (A : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) (i j : Fin n) :
    adjCoeff A d i j = ((Matrix.charmatrix A).adjugate i j).coeff d :=
  matPolyEquiv_coeff_apply _ _ _ _

theorem adjugate_eq_updateCol_det {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (i j : ι) :
    M.adjugate i j = (M.updateCol i (Pi.single j 1)).det := by
  have h := Matrix.adjugate_apply M.transpose j i
  rw [← Matrix.adjugate_transpose, Matrix.transpose_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose] at h
  exact h

theorem adjugate_natDegree (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    ((Matrix.charmatrix A).adjugate i j).natDegree ≤ n - 1 := by
  rw [adjugate_eq_updateCol_det, Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  apply (Polynomial.natDegree_smul_le _ _).trans
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  apply Polynomial.natDegree_mul_le.trans
  have hc : ((Matrix.charmatrix A).updateCol i (Pi.single j 1) (σ i) i).natDegree = 0 := by
    rw [Matrix.updateCol_self, Pi.single_apply]
    split_ifs <;> simp
  rw [hc, Nat.add_zero]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin n)).erase i, 1 := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)]
      apply (Matrix.charmatrix_apply_natDegree_le (M := A) _ _).trans
      split_ifs <;> omega
    _ = n - 1 := by simp

theorem adjCoeff_eq_zero (A : Matrix (Fin n) (Fin n) ℤ) {d : ℕ} (hd : n ≤ d) :
    adjCoeff A d = 0 := by
  ext i j
  rw [adjCoeff_apply, Matrix.zero_apply]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hi := i.isLt
  exact (adjugate_natDegree A i j).trans_lt (by omega)

theorem adjCoeff_recurrence (A : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) :
    adjCoeff A d - A * adjCoeff A (d + 1) = Matrix.scalar (Fin n) (A.charpoly.coeff (d + 1)) := by
  have h := congrArg matPolyEquiv (Matrix.mul_adjugate (Matrix.charmatrix A))
  rw [map_mul, Matrix.matPolyEquiv_charmatrix, matPolyEquiv_smul_one] at h
  have hc := congrArg (fun p => Polynomial.coeff p (d + 1)) h
  simpa only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_map, adjCoeff,
    Matrix.charpoly, algebraMap_matrix_apply] using hc

theorem adjCoeff_constant (A : Matrix (Fin n) (Fin n) ℤ) :
    -(A * adjCoeff A 0) = Matrix.scalar (Fin n) (A.charpoly.coeff 0) := by
  have h := congrArg matPolyEquiv (Matrix.mul_adjugate (Matrix.charmatrix A))
  rw [map_mul, Matrix.matPolyEquiv_charmatrix, matPolyEquiv_smul_one] at h
  have hc := congrArg (fun p => Polynomial.coeff p 0) h
  simpa only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero,
    Polynomial.coeff_C_mul, Polynomial.coeff_map, zero_sub, adjCoeff,
    Matrix.charpoly, algebraMap_matrix_apply] using hc

theorem adjCoeff_leading (A : Matrix (Fin n) (Fin n) ℤ) (hn : 0 < n) :
    adjCoeff A (n - 1) = 1 := by
  have h := adjCoeff_recurrence A (n - 1)
  rw [Nat.sub_add_cancel hn, adjCoeff_eq_zero A (le_refl n), mul_zero, sub_zero] at h
  have hc : A.charpoly.coeff n = 1 := by
    simpa [Polynomial.leadingCoeff] using A.charpoly_monic.leadingCoeff
  simpa [hc] using h

theorem trace_adjCoeff (A : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) :
    (adjCoeff A d).trace = A.charpoly.coeff (d + 1) * (d + 1 : ℕ) := by
  have h := congrArg (fun p => Polynomial.coeff p d) (derivative_charpoly A)
  simpa only [Polynomial.coeff_derivative, Matrix.trace, Polynomial.finset_sum_coeff,
    Matrix.diag_apply, adjCoeff_apply] using h.symm

theorem trace_scalar (c : ℤ) :
    (Matrix.scalar (Fin n) c).trace = (n : ℤ) * c := by
  change (Matrix.diagonal (fun _ : Fin n => c)).trace = _
  rw [Matrix.trace_diagonal]
  simp

theorem trace_mul_adjCoeff (A : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) :
    (A * adjCoeff A d).trace = ((d : ℤ) - n) * A.charpoly.coeff d := by
  cases d with
  | zero =>
    have h := congrArg Matrix.trace (adjCoeff_constant A)
    rw [Matrix.trace_neg, trace_scalar] at h
    simp only [Nat.cast_zero, zero_sub]
    linear_combination -h
  | succ d =>
    have h := congrArg Matrix.trace (adjCoeff_recurrence A d)
    rw [Matrix.trace_sub, trace_adjCoeff, trace_scalar] at h
    push_cast at h ⊢
    linear_combination -h

end HiddenCircuits.Complexity.DeterminantRuntime
