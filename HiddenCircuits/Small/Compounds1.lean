import HiddenCircuits.Small.States
import HiddenCircuits.PermutationEnumeration
namespace HiddenCircuits.Small
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def F1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 1, 1], ![0, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]]


def Inv1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, -1, 0, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 0, 1]]


theorem compound_upper1 : compress enum1 (compound (upper 4)) = F1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum1_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem inverse_upper1 : compress enum1 (upperInverse 4 1) = Inv1 := by
  exact compress_upperInverse enum1 F1 Inv1 compound_upper1 (by decide +kernel)

def V1_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 1, 1], ![1, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]]


def R1_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]


theorem compound_V1_0 : compress enum1 (compound (addedCut (n:=4) 0)) = V1_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum1_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise1_0 : compress enum1 (rise 4 1 0) = R1_0 := by
  rw [rise, compress_mul, compound_V1_0, inverse_upper1]
  decide +kernel

def Z1_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]]


def D1_0 : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]


theorem compound_Z1_0 : compress enum1 (compound (deletedCut (n:=4) 0)) = Z1_0 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum1_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop1_0 : compress enum1 (drop 4 1 0) = D1_0 := by
  rw [drop, compress_mul, compound_Z1_0, inverse_upper1]
  decide +kernel

def V1_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 0, 0, 1]]


def R1_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]


theorem compound_V1_1 : compress enum1 (compound (addedCut (n:=4) 1)) = V1_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum1_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise1_1 : compress enum1 (rise 4 1 1) = R1_1 := by
  rw [rise, compress_mul, compound_V1_1, inverse_upper1]
  decide +kernel

def Z1_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 1]]


def D1_1 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]


theorem compound_Z1_1 : compress enum1 (compound (deletedCut (n:=4) 1)) = Z1_1 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum1_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop1_1 : compress enum1 (drop 4 1 1) = D1_1 := by
  rw [drop, compress_mul, compound_Z1_1, inverse_upper1]
  decide +kernel

def V1_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 1, 1], ![0, 1, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1]]


def R1_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0]]


theorem compound_V1_2 : compress enum1 (compound (addedCut (n:=4) 2)) = V1_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum1_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rise1_2 : compress enum1 (rise 4 1 2) = R1_2 := by
  rw [rise, compress_mul, compound_V1_2, inverse_upper1]
  decide +kernel

def Z1_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 1, 1, 1], ![0, 1, 1, 1], ![0, 0, 0, 1], ![0, 0, 0, 1]]


def D1_2 : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 1]]


theorem compound_Z1_2 : compress enum1 (compound (deletedCut (n:=4) 2)) = Z1_2 := by
  ext a b
  simp only [compress, Matrix.submatrix_apply, compound, permanent_eq_explicit, enum1_track]
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem drop1_2 : compress enum1 (drop 4 1 2) = D1_2 := by
  rw [drop, compress_mul, compound_Z1_2, inverse_upper1]
  decide +kernel


end HiddenCircuits.Small
