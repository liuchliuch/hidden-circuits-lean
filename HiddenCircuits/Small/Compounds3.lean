import HiddenCircuits.Small.States
import HiddenCircuits.PermutationEnumeration
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def F3 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 2, 4], ![0, 1, 1, 2], ![0, 0, 1, 1], ![0, 0, 0, 1]]


def Inv3 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, -1, -1, -1], ![0, 1, -1, -1], ![0, 0, 1, -1], ![0, 0, 0, 1]]


theorem compound_upper3 : compress enum3 (compound (upper 4)) = F3 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum3_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem inverse_upper3 : compress enum3 (upperInverse 4 3) = Inv3 := by
  exact compress_upperInverse enum3 F3 Inv3 compound_upper3 (by decide +kernel)

def V3_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![2, 2, 4, 4], ![0, 2, 2, 2], ![0, 0, 1, 1], ![0, 0, 1, 1]]


def R3_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![2, 0, 0, -4], ![0, 2, 0, -2], ![0, 0, 1, 0], ![0, 0, 1, 0]]


theorem compound_V3_0 : compress enum3 (compound (addedCut (n:=4) 0)) = V3_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum3_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise3_0 : compress enum3 (rise 4 3 0) = R3_0 := by
  rw [rise, compress_mul, compound_V3_0, inverse_upper3]
  decide +kernel

def Z3_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 4], ![0, 0, 0, 2], ![0, 0, 0, 1], ![0, 0, 0, 1]]


def D3_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 4], ![0, 0, 0, 2], ![0, 0, 0, 1], ![0, 0, 0, 1]]


theorem compound_Z3_0 : compress enum3 (compound (deletedCut (n:=4) 0)) = Z3_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum3_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop3_0 : compress enum3 (drop 4 3 0) = D3_0 := by
  rw [drop, compress_mul, compound_Z3_0, inverse_upper3]
  decide +kernel

def V3_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![2, 2, 2, 6], ![0, 1, 1, 2], ![0, 1, 1, 2], ![0, 0, 0, 2]]


def R3_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![2, 0, -2, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 2]]


theorem compound_V3_1 : compress enum3 (compound (addedCut (n:=4) 1)) = V3_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum3_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise3_1 : compress enum3 (rise 4 3 1) = R3_1 := by
  rw [rise, compress_mul, compound_V3_1, inverse_upper3]
  decide +kernel

def Z3_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 2, 2], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 0]]


def D3_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 2, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]]


theorem compound_Z3_1 : compress enum3 (compound (deletedCut (n:=4) 1)) = Z3_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum3_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop3_1 : compress enum3 (drop 4 3 1) = D3_1 := by
  rw [drop, compress_mul, compound_Z3_1, inverse_upper3]
  decide +kernel

def V3_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 2, 4], ![1, 1, 2, 4], ![0, 0, 2, 2], ![0, 0, 0, 2]]


def R3_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]]


theorem compound_V3_2 : compress enum3 (compound (addedCut (n:=4) 2)) = V3_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum3_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise3_2 : compress enum3 (rise 4 3 2) = R3_2 := by
  rw [rise, compress_mul, compound_V3_2, inverse_upper3]
  decide +kernel

def Z3_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 1, 1, 2], ![0, 1, 1, 2], ![0, 0, 0, 0], ![0, 0, 0, 0]]


def D3_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]


theorem compound_Z3_2 : compress enum3 (compound (deletedCut (n:=4) 2)) = Z3_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum3_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop3_2 : compress enum3 (drop 4 3 2) = D3_2 := by
  rw [drop, compress_mul, compound_Z3_2, inverse_upper3]
  decide +kernel


end HiddenCircuits.Small
