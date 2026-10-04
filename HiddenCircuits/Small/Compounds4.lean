import HiddenCircuits.Small.States
import HiddenCircuits.PermutationEnumeration
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def F4 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


def Inv4 : Matrix (Fin 1) (Fin 1) ℚ := ![![1]]


theorem compound_upper4 : compress enum4 (compound (upper 4)) = F4 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum4_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem inverse_upper4 : compress enum4 (upperInverse 4 4) = Inv4 := by
  exact compress_upperInverse enum4 F4 Inv4 compound_upper4 (by decide +kernel)

def V4_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


def R4_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


theorem compound_V4_0 : compress enum4 (compound (addedCut (n:=4) 0)) = V4_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum4_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise4_0 : compress enum4 (rise 4 4 0) = R4_0 := by
  rw [rise, compress_mul, compound_V4_0, inverse_upper4]
  decide +kernel

def Z4_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


def D4_0 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem compound_Z4_0 : compress enum4 (compound (deletedCut (n:=4) 0)) = Z4_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum4_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop4_0 : compress enum4 (drop 4 4 0) = D4_0 := by
  rw [drop, compress_mul, compound_Z4_0, inverse_upper4]
  decide +kernel

def V4_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


def R4_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


theorem compound_V4_1 : compress enum4 (compound (addedCut (n:=4) 1)) = V4_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum4_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise4_1 : compress enum4 (rise 4 4 1) = R4_1 := by
  rw [rise, compress_mul, compound_V4_1, inverse_upper4]
  decide +kernel

def Z4_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


def D4_1 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem compound_Z4_1 : compress enum4 (compound (deletedCut (n:=4) 1)) = Z4_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum4_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop4_1 : compress enum4 (drop 4 4 1) = D4_1 := by
  rw [drop, compress_mul, compound_Z4_1, inverse_upper4]
  decide +kernel

def V4_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


def R4_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![2]]


theorem compound_V4_2 : compress enum4 (compound (addedCut (n:=4) 2)) = V4_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum4_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise4_2 : compress enum4 (rise 4 4 2) = R4_2 := by
  rw [rise, compress_mul, compound_V4_2, inverse_upper4]
  decide +kernel

def Z4_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


def D4_2 : Matrix (Fin 1) (Fin 1) ℚ := ![![0]]


theorem compound_Z4_2 : compress enum4 (compound (deletedCut (n:=4) 2)) = Z4_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum4_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop4_2 : compress enum4 (drop 4 4 2) = D4_2 := by
  rw [drop, compress_mul, compound_Z4_2, inverse_upper4]
  decide +kernel


end HiddenCircuits.Small
