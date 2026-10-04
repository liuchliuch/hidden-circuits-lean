import HiddenCircuits.Small.Gate8Sparse
namespace HiddenCircuits.Small

/-- Ordered insertion combines equal coordinates and removes zero coefficients. -/
def sparseInsert {m : ℕ} (x : Fin m × ℚ) (xs : List (Fin m × ℚ)) : List (Fin m × ℚ) :=
  if x.2 = 0 then xs else
  match xs with
  | [] => [x]
  | y::ys => if x.1 = y.1 then
      if x.2 + y.2 = 0 then ys else (x.1,x.2+y.2)::ys
    else if x.1 < y.1 then x::xs else y::sparseInsert x ys

theorem sparseRow_insert {m : ℕ} (x : Fin m × ℚ) (xs : List (Fin m × ℚ)) (j : Fin m) :
    sparseRow (sparseInsert x xs) j = (if x.1 = j then x.2 else 0) + sparseRow xs j := by
  induction xs with
  | nil =>
    simp only [sparseInsert, sparseRow]
    split_ifs <;> simp_all [sparseRow]
  | cons y ys ih =>
    by_cases hc : x.2 = 0
    · rw [sparseInsert, if_pos hc]
      simp [hc]
    · rw [sparseInsert, if_neg hc]
      by_cases hk : x.1 = y.1
      · rw [if_pos hk]
        by_cases hz : x.2 + y.2 = 0
        · rw [if_pos hz]
          by_cases hj : x.1 = j
          · have hy : y.1 = j := hk.symm.trans hj
            simp only [sparseRow, hj, hy, if_true]
            linear_combination -hz
          · have hy : y.1 ≠ j := fun hy => hj (hk.trans hy)
            simp [sparseRow, hj, hy]
        · rw [if_neg hz]
          by_cases hj : x.1 = j
          · have hy : y.1 = j := hk.symm.trans hj
            simp [sparseRow, hj, hy, add_assoc]
          · have hy : y.1 ≠ j := fun hy => hj (hk.trans hy)
            simp [sparseRow, hj, hy]
      · rw [if_neg hk]
        by_cases hlt : x.1 < y.1
        · rw [if_pos hlt]
          rfl
        · rw [if_neg hlt]
          simp only [sparseRow, ih]
          ring

def sparseNormalize {m : ℕ} (xs : List (Fin m × ℚ)) : List (Fin m × ℚ) :=
  xs.foldr sparseInsert []

theorem sparseRow_normalize {m : ℕ} (xs : List (Fin m × ℚ)) (j : Fin m) :
    sparseRow (sparseNormalize xs) j = sparseRow xs j := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change sparseRow (sparseInsert x (sparseNormalize xs)) j = _
    rw [sparseRow_insert, ih]
    rfl

theorem sparseRow_append {m : ℕ} (xs ys : List (Fin m × ℚ)) (j : Fin m) :
    sparseRow (xs ++ ys) j = sparseRow xs j + sparseRow ys j := by
  induction xs with
  | nil => simp [sparseRow]
  | cons x xs ih => simp [sparseRow, ih, add_assoc]

theorem sparseRow_scale {m : ℕ} (xs : List (Fin m × ℚ)) (c : ℚ) (j : Fin m) :
    sparseRow (xs.map (fun x => (x.1,c*x.2))) j = c * sparseRow xs j := by
  induction xs with
  | nil => simp [sparseRow]
  | cons x xs ih =>
    simp only [List.map_cons, sparseRow, ih, mul_add]
    split_ifs <;> ring

def sparseMultiplyRow {m p : ℕ} (xs : List (Fin m × ℚ))
    (b : Fin m → List (Fin p × ℚ)) : List (Fin p × ℚ) :=
  sparseNormalize (xs.flatMap (fun x => (b x.1).map (fun y => (y.1,x.2*y.2))))

theorem sparseRow_multiply {m p : ℕ} (xs : List (Fin m × ℚ))
    (b : Fin m → List (Fin p × ℚ)) (j : Fin p) :
    sparseRow (sparseMultiplyRow xs b) j =
      (xs.map (fun x => x.2 * sparseRow (b x.1) j)).sum := by
  unfold sparseMultiplyRow
  rw [sparseRow_normalize]
  induction xs with
  | nil => simp [sparseRow]
  | cons x xs ih =>
    simp only [List.flatMap_cons, sparseRow_append, sparseRow_scale, ih,
      List.map_cons, List.sum_cons]

theorem sparseMatrix_mul_sparseMatrix {n m p : ℕ}
    (a : Fin n → List (Fin m × ℚ)) (b : Fin m → List (Fin p × ℚ)) :
    sparseMatrix a * sparseMatrix b = sparseMatrix (fun i => sparseMultiplyRow (a i) b) := by
  rw [sparseMatrix_mul]
  ext i j
  exact (sparseRow_multiply (a i) b j).symm

end HiddenCircuits.Small
