import HiddenCircuits.Circuit.SharedDiagonal
import HiddenCircuits.Circuit.SpectralCircuit

namespace HiddenCircuits.Circuit
open scoped Kronecker

/-- Tensor-local diagonal gates are genuine global diagonal gates in the selected wire values. -/
theorem Placement.lift_diagonal {n d : ℕ} (p : Placement n d) (v : CodeBits d → ℚ) :
    p.lift (Matrix.diagonal v) = Matrix.diagonal (fun x => v (p.equiv.symm x).2.1) := by
  ext x y
  by_cases h:x=y
  · subst y
    simp [Placement.lift,Matrix.kroneckerMap_apply,Matrix.diagonal_apply,Matrix.one_apply]
  · have he : p.equiv.symm x ≠ p.equiv.symm y := fun he => h (p.equiv.symm.injective he)
    simp only [Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.diagonal_apply,if_neg h]
    by_cases h1:(p.equiv.symm x).1=(p.equiv.symm y).1 <;>
      by_cases h2:(p.equiv.symm x).2.1=(p.equiv.symm y).2.1 <;>
      by_cases h3:(p.equiv.symm x).2.2=(p.equiv.symm y).2.2 <;>
      simp [h1,h2,h3]
    exact False.elim (he (Prod.ext h1 (Prod.ext h2 h3)))

 theorem Placement.lift_pow {n d : ℕ} (p : Placement n d)
    (A : Matrix (CodeBits d) (CodeBits d) ℚ) (r : ℕ) : p.lift (A^r)=(p.lift A)^r := by
  induction r with
  | zero => exact p.lift_one
  | succ r ih => rw [pow_succ,p.lift_mul,ih,pow_succ]

 theorem reindex_pow {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ≃ ι) (M : Matrix ι ι ℚ) (r : ℕ) :
    (M^r).submatrix e e=(M.submatrix e e)^r := by
  induction r with
  | zero => ext i j; simp [Matrix.one_apply,e.injective.eq_iff]
  | succ r ih => rw [pow_succ,Matrix.submatrix_mul _ _ _ _ _ e.bijective,ih,pow_succ]

 theorem reindex_diagonal {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : κ ≃ ι) (v : ι → ℚ) : (Matrix.diagonal v).submatrix e e=Matrix.diagonal (v ∘ e) := by
  ext i j
  simp [Matrix.diagonal_apply,e.injective.eq_iff]

/-- The three actual squared eigenvalue classes00/10,01,11. -/
def localSpectralClass (x : CodeBits 2) : Fin 3 := ![0,1,0,2] (twoBitEquiv.symm x)

def Placement.spectralClass {n : ℕ} (p : Placement n 2) (x : CodeBits n) : Fin 3 :=
  localSpectralClass (p.equiv.symm x).2.1

 theorem delta_even_power (r : ℕ) : delta^(2*r)=Matrix.diagonal ![(4:ℚ)^r,9^r,4^r,1] := by
  rw [delta,Matrix.diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> norm_num [pow_mul]

 theorem logicalDelta_even_power (r : ℕ) : logicalDelta^(2*r)=Matrix.diagonal
    (fun x => if localSpectralClass x=0 then (4:ℚ)^r else if localSpectralClass x=1 then (9:ℚ)^r else 1) := by
  rw [logicalDelta,← reindex_pow,delta_even_power,reindex_diagonal]
  congr 1
  funext x
  obtain ⟨a,rfl⟩ := twoBitEquiv.surjective x
  fin_cases a <;> simp [localSpectralClass]

/-- The actual available Δ powers give exactly the three-eigenvalue sample matrix. -/
theorem placed_delta_even_power {n : ℕ} (p : Placement n 2) (r : ℕ) :
    (p.lift logicalDelta)^(2*r)=SpectralGate.sample r (.marked p.spectralClass) := by
  rw [← p.lift_pow,logicalDelta_even_power,p.lift_diagonal]
  rfl

/-- N and CZ are z=0 and z=−1 of this literal diagonal constraint. -/
def constraintDiagonal (z : ℚ) : Matrix (Fin 4) (Fin 4) ℚ := Matrix.diagonal ![1,1,1,z]
def logicalConstraint (z : ℚ) : Matrix (CodeBits 2) (CodeBits 2) ℚ :=
  (constraintDiagonal z).submatrix twoBitEquiv.symm twoBitEquiv.symm

 theorem logicalConstraint_diagonal (z : ℚ) : logicalConstraint z = Matrix.diagonal
    (fun x => if localSpectralClass x=0 ∨ localSpectralClass x=1 then 1 else z) := by
  rw [logicalConstraint,constraintDiagonal,reindex_diagonal]
  congr 1
  funext x
  obtain ⟨a,rfl⟩ := twoBitEquiv.surjective x
  fin_cases a <;> simp [localSpectralClass]

 theorem placed_constraint_target {n : ℕ} (p : Placement n 2) (z : ℚ) :
    p.lift (logicalConstraint z)=SpectralGate.target z (.marked p.spectralClass) := by
  rw [logicalConstraint_diagonal,p.lift_diagonal]
  rfl

end HiddenCircuits.Circuit
