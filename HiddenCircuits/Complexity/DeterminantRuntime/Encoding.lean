import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime
import Mathlib.LinearAlgebra.Matrix.Defs

/-! Canonical row-major signed integer matrix encoding.  -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open BinaryArithmetic
variable {n : ℕ}

def matrixWords (A : Matrix (Fin n) (Fin n) ℤ) : List BitString :=
  (List.ofFn fun i => List.ofFn fun j => signedBits (A i j)).flatten

def matrixInput (A : Matrix (Fin n) (Fin n) ℤ) : BitString :=
  pairBits (List.replicate n true) (encodeBitList (matrixWords A))

@[simp] theorem matrixWords_length (A : Matrix (Fin n) (Fin n) ℤ) :
    (matrixWords A).length = n * n := by
  simp [matrixWords, List.length_flatten, Function.comp_def]

@[simp] theorem matrixInput_length (A : Matrix (Fin n) (Fin n) ℤ) :
    (matrixInput A).length = 2 * n + (encodeBitList (matrixWords A)).length + 1 := by
  simp [matrixInput]

theorem dimension_le_input (A : Matrix (Fin n) (Fin n) ℤ) : n ≤ (matrixInput A).length := by
  rw [matrixInput_length]
  omega

theorem array_length_le_input (A : Matrix (Fin n) (Fin n) ℤ) :
    (encodeBitList (matrixWords A)).length ≤ (matrixInput A).length := by
  rw [matrixInput_length]
  omega

theorem dimension_square_le_array (A : Matrix (Fin n) (Fin n) ℤ) :
    n * n ≤ (encodeBitList (matrixWords A)).length := by
  simpa using list_length_le_encodeBitList_length (matrixWords A)

theorem entry_mem_matrixWords (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    signedBits (A i j) ∈ matrixWords A := by
  apply List.mem_flatten.mpr
  refine ⟨List.ofFn (fun j => signedBits (A i j)), ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · exact List.mem_ofFn.mpr ⟨j, rfl⟩

theorem entry_length_le_input (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (signedBits (A i j)).length ≤ (matrixInput A).length :=
  (member_length_le_encodeBitList (entry_mem_matrixWords A i j)).trans (array_length_le_input A)

theorem entry_abs_le_input_pow (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (A i j).natAbs ≤ 2 ^ (matrixInput A).length :=
  abs_le_pow_signed_length _ _ (entry_length_le_input A i j)

end HiddenCircuits.Complexity.DeterminantRuntime
