import HiddenCircuits.SmallCertificates
import Mathlib.LinearAlgebra.Matrix.Rank

namespace HiddenCircuits
open Small

/-- Lemma 5.1, vanishing on the actual zero-particle sector. -/
theorem localFilter_zero : localFilter 0 = 0 := by
  apply compress_injective enum0
  rw [localFilter0]
  decide +kernel

/-- Lemma 5.1, vanishing on the actual one-particle sector. -/
theorem localFilter_one : localFilter 1 = 0 := by
  apply compress_injective enum1
  rw [localFilter1]
  decide +kernel

/-- The entire two-particle table is connected to the original twenty-letter word. -/
theorem localFilter_table (i j : Fin 6) :
    localFilter 2 (enum2 i) (enum2 j) = Theta2 i j :=
  congrFun (congrFun localFilter2 i) j

/-- Lemma 5.1, actual permanental-filter idempotence. -/
theorem localFilter_idempotent : localFilter 2 * localFilter 2 = localFilter 2 := by
  apply compress_injective enum2
  rw [compress_mul, localFilter2]
  decide +kernel

def filterImageColumns : Matrix (Fin 6) (Fin 2) ℚ :=
  ![![1,0], ![1,0], ![-1,0], ![0,1], ![0,1/2], ![0,1/2]]

def filterCodeRows : Matrix (Fin 2) (Fin 6) ℚ :=
  ![![0,1,0,0,0,0], ![0,0,0,1,0,0]]

/-- The rank calculation has explicit two-dimensional factors and a verified left inverse. -/
theorem localFilter_rank : (localFilter 2).rank = 2 := by
  have hf : Theta2 = filterImageColumns * filterCodeRows := by decide +kernel
  have hi : filterCodeRows * Theta2 * filterImageColumns = 1 := by decide +kernel
  have hu : Theta2.rank ≤ 2 := by
    rw [hf]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
  have hl : 2 ≤ Theta2.rank := by
    have h₁ := Matrix.rank_mul_le_left (filterCodeRows * Theta2) filterImageColumns
    have h₂ := Matrix.rank_mul_le_right filterCodeRows Theta2
    rw [hi, Matrix.rank_one, Fintype.card_fin] at h₁
    exact h₁.trans h₂
  have hr : (compress enum2 (localFilter 2)).rank = (localFilter 2).rank :=
    Matrix.rank_submatrix _ enum2 enum2
  rw [localFilter2] at hr
  omega

/-- The logical zero row is the actual state 1010. -/
theorem localFilter_fixes_zero : ∀ T,
    localFilter 2 (states2 1) T = if T = states2 1 then 1 else 0 := by
  intro T
  obtain ⟨j,rfl⟩ := enum2.surjective T
  change localFilter 2 (enum2 1) (enum2 j) = _
  rw [localFilter_table]
  fin_cases j <;> decide +kernel

/-- The logical one row is the actual state 0110. -/
theorem localFilter_fixes_one : ∀ T,
    localFilter 2 (states2 3) T = if T = states2 3 then 1 else 0 := by
  intro T
  obtain ⟨j,rfl⟩ := enum2.surjective T
  change localFilter 2 (enum2 3) (enum2 j) = _
  rw [localFilter_table]
  fin_cases j <;> decide +kernel

end HiddenCircuits
