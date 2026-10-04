import HiddenCircuits.Complexity.DeterminantRuntime.Gather
import HiddenCircuits.Complexity.DeterminantRuntime.Encoding
import Mathlib.Data.List.OfFn

/-! Row, column, and diagonal semantics of the actual strided word gather. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open BinaryArithmetic
variable {n : ℕ}

theorem matrixWords_ofFn (A : Matrix (Fin n) (Fin n) ℤ) :
    matrixWords A = List.ofFn (fun p : Fin (n*n) => signedBits (A p.divNat p.modNat)) := by
  rw [List.ofFn_mul]
  unfold matrixWords
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  congr 2
  · apply Fin.ext
    simp only [Fin.divNat, Fin.val_mk]
    rw [Nat.mul_comm i.val n, Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  · apply Fin.ext
    simp [Fin.modNat, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

theorem matrixWords_get (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (matrixWords A)[i.val*n+j.val]?.getD [] = signedBits (A i j) := by
  have h : i.val*n+j.val < n*n := by nlinarith [i.isLt,j.isLt]
  rw [matrixWords_ofFn, List.getElem?_ofFn, dif_pos h]
  simp only [Option.getD_some]
  congr 2
  · apply Fin.ext
    simp only [Fin.divNat, Fin.val_mk]
    rw [Nat.mul_comm i.val n, Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  · apply Fin.ext
    simp [Fin.modNat, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

theorem gather_words_ofFn (ws : List BitString) (f : Fin n → BitString) (start stride : ℕ)
    (h : ∀ i : Fin n, ws[start+stride*i.val]?.getD [] = f i) :
    Gather.words ws start stride n = List.ofFn f := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    rw [Gather.words, List.ofFn_succ]
    congr 1
    · simpa using h 0
    · apply ih
      intro i
      have hi := h i.succ
      simpa [Fin.val_succ, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi

theorem gather_row (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    Gather.words (matrixWords A) (i.val*n) 1 n = List.ofFn (fun j => signedBits (A i j)) := by
  apply gather_words_ofFn
  intro j
  simpa using matrixWords_get A i j

theorem gather_column (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    Gather.words (matrixWords A) j.val n n = List.ofFn (fun i => signedBits (A i j)) := by
  apply gather_words_ofFn
  intro i
  simpa [Nat.add_comm, Nat.mul_comm] using matrixWords_get A i j

theorem gather_diagonal (A : Matrix (Fin n) (Fin n) ℤ) :
    Gather.words (matrixWords A) 0 (n+1) n = List.ofFn (fun i => signedBits (A i i)) := by
  apply gather_words_ofFn
  intro i
  simpa [Nat.add_mul, Nat.mul_add, Nat.mul_comm] using matrixWords_get A i i

end HiddenCircuits.Complexity.DeterminantRuntime
