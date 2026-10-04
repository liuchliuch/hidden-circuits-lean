import HiddenCircuits.PermutationEnumeration

namespace HiddenCircuits.Small
open scoped BigOperators

/-- Sparse rows are certificates for ordinary finite matrices. Duplicate positions add. -/
def sparseRow {m : ℕ} : List (Fin m × ℚ) → Fin m → ℚ
  | [], _ => 0
  | (k,c)::xs, j => (if k = j then c else 0) + sparseRow xs j

def sparseMatrix {n m : ℕ} (a : Fin n → List (Fin m × ℚ)) :
    Matrix (Fin n) (Fin m) ℚ := fun i => sparseRow (a i)

/-- The sparse evaluation computes the ordinary matrix product exactly. -/
theorem sparseRow_mul {m p : ℕ} (xs : List (Fin m × ℚ))
    (B : Matrix (Fin m) (Fin p) ℚ) (j : Fin p) :
    (∑ k, sparseRow xs k * B k j) =
      (xs.map (fun a => a.2 * B a.1 j)).sum := by
  induction xs with
  | nil => simp [sparseRow]
  | cons x xs ih =>
    rcases x with ⟨k,c⟩
    simp only [sparseRow, add_mul, Finset.sum_add_distrib, ih,
      List.map_cons, List.sum_cons]
    congr 1
    simp [ite_mul]

def sparseProduct {n m p : ℕ} (a : Fin n → List (Fin m × ℚ))
    (B : Matrix (Fin m) (Fin p) ℚ) : Matrix (Fin n) (Fin p) ℚ :=
  fun i j => ((a i).map (fun x => x.2 * B x.1 j)).sum

theorem sparseMatrix_mul {n m p : ℕ} (a : Fin n → List (Fin m × ℚ))
    (B : Matrix (Fin m) (Fin p) ℚ) :
    sparseMatrix a * B = sparseProduct a B := by
  ext i j
  exact sparseRow_mul (a i) B j

/-- A candidate normalized transfer is identified using the already proved finite inverse. -/
theorem normalized_of_mul_upper {n q d : ℕ} (e : Fin d ≃ State n q)
    (A : Matrix (Fin n) (Fin n) ℚ) (R : Matrix (Fin d) (Fin d) ℚ)
    (h : R * compress e (compound (upper n)) = compress e (compound A)) :
    compress e (compound A * upperInverse n q) = R := by
  rw [compress_mul, ← h, Matrix.mul_assoc, ← compress_mul, mul_upperInverse,
    compress_one, mul_one]

end HiddenCircuits.Small
