import HiddenCircuits.Small.States
import HiddenCircuits.PermutationEnumeration
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def F0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def Inv0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_upper0 : compress enum0 (compound (upper 4)) = F0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum0_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem inverse_upper0 : compress enum0 (upperInverse 4 0) = Inv0 := by
  exact compress_upperInverse enum0 F0 Inv0 compound_upper0 (by decide +kernel)

def V0_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def R0_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_V0_0 : compress enum0 (compound (addedCut (n:=4) 0)) = V0_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum0_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise0_0 : compress enum0 (rise 4 0 0) = R0_0 := by
  rw [rise, compress_mul, compound_V0_0, inverse_upper0]
  decide +kernel

def Z0_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def D0_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_Z0_0 : compress enum0 (compound (deletedCut (n:=4) 0)) = Z0_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum0_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop0_0 : compress enum0 (drop 4 0 0) = D0_0 := by
  rw [drop, compress_mul, compound_Z0_0, inverse_upper0]
  decide +kernel

def V0_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def R0_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_V0_1 : compress enum0 (compound (addedCut (n:=4) 1)) = V0_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum0_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise0_1 : compress enum0 (rise 4 0 1) = R0_1 := by
  rw [rise, compress_mul, compound_V0_1, inverse_upper0]
  decide +kernel

def Z0_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def D0_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_Z0_1 : compress enum0 (compound (deletedCut (n:=4) 1)) = Z0_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum0_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop0_1 : compress enum0 (drop 4 0 1) = D0_1 := by
  rw [drop, compress_mul, compound_Z0_1, inverse_upper0]
  decide +kernel

def V0_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def R0_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_V0_2 : compress enum0 (compound (addedCut (n:=4) 2)) = V0_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum0_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise0_2 : compress enum0 (rise 4 0 2) = R0_2 := by
  rw [rise, compress_mul, compound_V0_2, inverse_upper0]
  decide +kernel

def Z0_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def D0_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_Z0_2 : compress enum0 (compound (deletedCut (n:=4) 2)) = Z0_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum0_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop0_2 : compress enum0 (drop 4 0 2) = D0_2 := by
  rw [drop, compress_mul, compound_Z0_2, inverse_upper0]
  decide +kernel


end HiddenCircuits.Small
