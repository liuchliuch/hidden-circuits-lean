import HiddenCircuits.Small.States
import HiddenCircuits.PermutationEnumeration
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def F2 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 1, 1, 2, 2, 2], ![0, 1, 1, 1, 1, 2], ![0, 0, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1]]


def Inv2 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, -1, 0, -1, 0, 2], ![0, 1, -1, -1, 1, 0], ![0, 0, 1, 0, -1, 0], ![0, 0, 0, 1, -1, -1], ![0, 0, 0, 0, 1, -1], ![0, 0, 0, 0, 0, 1]]


theorem compound_upper2 : compress enum2 (compound (upper 4)) = F2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum2_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem inverse_upper2 : compress enum2 (upperInverse 4 2) = Inv2 := by
  exact compress_upperInverse enum2 F2 Inv2 compound_upper2 (by decide +kernel)

def V2_0 : Matrix (Fin 6) (Fin 6) ℚ := ![![2, 2, 2, 2, 2, 2], ![0, 1, 1, 1, 1, 2], ![0, 0, 1, 0, 1, 1], ![0, 1, 1, 1, 1, 2], ![0, 0, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 1]]


def R2_0 : Matrix (Fin 6) (Fin 6) ℚ := ![![2, 0, 0, -2, 0, 2], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]


theorem compound_V2_0 : compress enum2 (compound (addedCut (n:=4) 0)) = V2_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum2_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise2_0 : compress enum2 (rise 4 2 0) = R2_0 := by
  rw [rise, compress_mul, compound_V2_0, inverse_upper2]
  decide +kernel

def Z2_0 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 2, 2, 2], ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1]]


def D2_0 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 0, 0, 2, 0, -2], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]


theorem compound_Z2_0 : compress enum2 (compound (deletedCut (n:=4) 0)) = Z2_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum2_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop2_0 : compress enum2 (drop 4 2 0) = D2_0 := by
  rw [drop, compress_mul, compound_Z2_0, inverse_upper2]
  decide +kernel

def V2_1 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 1, 1, 2, 2, 2], ![1, 1, 1, 2, 2, 2], ![0, 0, 1, 0, 1, 1], ![0, 0, 0, 2, 2, 2], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1]]


def R2_1 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 2, 0, -2], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0]]


theorem compound_V2_1 : compress enum2 (compound (addedCut (n:=4) 1)) = V2_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum2_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise2_1 : compress enum2 (rise 4 2 1) = R2_1 := by
  rw [rise, compress_mul, compound_V2_1, inverse_upper2]
  decide +kernel

def Z2_1 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 1, 1, 1, 1, 2], ![0, 1, 1, 1, 1, 2], ![0, 0, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1]]


def D2_1 : Matrix (Fin 6) (Fin 6) ℚ := ![![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1]]


theorem compound_Z2_1 : compress enum2 (compound (deletedCut (n:=4) 1)) = Z2_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum2_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop2_1 : compress enum2 (drop 4 2 1) = D2_1 := by
  rw [drop, compress_mul, compound_Z2_1, inverse_upper2]
  decide +kernel

def V2_2 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 1, 1, 2, 2, 2], ![0, 1, 1, 1, 1, 2], ![0, 1, 1, 1, 1, 2], ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 2]]


def R2_2 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 2]]


theorem compound_V2_2 : compress enum2 (compound (addedCut (n:=4) 2)) = V2_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum2_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise2_2 : compress enum2 (rise 4 2 2) = R2_2 := by
  rw [rise, compress_mul, compound_V2_2, inverse_upper2]
  decide +kernel

def Z2_2 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 1, 1, 2, 2, 2], ![0, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0]]


def D2_2 : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0]]


theorem compound_Z2_2 : compress enum2 (compound (deletedCut (n:=4) 2)) = Z2_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum2_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop2_2 : compress enum2 (drop 4 2 2) = D2_2 := by
  rw [drop, compress_mul, compound_Z2_2, inverse_upper2]
  decide +kernel


end HiddenCircuits.Small
