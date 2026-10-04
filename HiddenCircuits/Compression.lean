import HiddenCircuits.Transfers

namespace HiddenCircuits
variable {n q d : ℕ}

def compress (e : Fin d ≃ State n q) (M : Matrix (State n q) (State n q) ℚ) :
    Matrix (Fin d) (Fin d) ℚ := M.submatrix e e

@[simp] theorem compress_mul (e : Fin d ≃ State n q)
    (M A : Matrix (State n q) (State n q) ℚ) :
    compress e (M * A) = compress e M * compress e A := by
  exact Matrix.submatrix_mul M A e e e e.bijective

@[simp] theorem compress_one (e : Fin d ≃ State n q) : compress e 1 = 1 := by
  ext i j
  simp [compress, Matrix.one_apply, e.injective.eq_iff]

@[simp] theorem compress_smul (e : Fin d ≃ State n q) (c : ℚ)
    (M : Matrix (State n q) (State n q) ℚ) :
    compress e (c • M) = c • compress e M := rfl

 theorem compress_injective (e : Fin d ≃ State n q) : Function.Injective (compress e) := by
  intro M A h
  ext S T
  obtain ⟨i,rfl⟩ := e.surjective S
  obtain ⟨j,rfl⟩ := e.surjective T
  exact congrFun (congrFun h i) j

 theorem compress_upperInverse (e : Fin d ≃ State n q) (F V : Matrix (Fin d) (Fin d) ℚ)
    (hF : compress e (compound (upper n)) = F) (hV : F * V = 1) :
    compress e (upperInverse n q) = V := by
  have hleft := congrArg (compress e) (upperInverse_mul n q)
  rw [compress_mul, compress_one, hF] at hleft
  calc
    compress e (upperInverse n q) = compress e (upperInverse n q) * (F * V) := by rw [hV, mul_one]
    _ = (compress e (upperInverse n q) * F) * V := by rw [Matrix.mul_assoc]
    _ = V := by rw [hleft, one_mul]

 theorem compress_word (e : Fin d ≃ State n q) (w : List (Letter n)) :
    compress e (wordMatrix q w) = (w.map (fun l => compress e (l.matrix q))).prod := by
  induction w with
  | nil => simp
  | cons l w ih => simp [ih]
end HiddenCircuits
