import HiddenCircuits.Transfers

namespace HiddenCircuits
open scoped BigOperators

/-- Standard coordinate columns for an injective choice of ambient coordinates. -/
def coordinateColumns {ι α : Type*} [DecidableEq ι] (e : α → ι) : Matrix ι α ℚ :=
  fun i a => if i=e a then 1 else 0

 theorem coordinateColumns_leftInverse {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (e : α → ι) (he : Function.Injective e) :
    (coordinateColumns e).transpose * coordinateColumns e = 1 := by
  ext a b
  simp only [Matrix.mul_apply,Matrix.transpose_apply,coordinateColumns,Matrix.one_apply]
  rw [Finset.sum_eq_single (e a)]
  · simp [he.eq_iff]
  · intro i _ hi
    simp [hi]
  · simp

/-- Extension by zero on all unselected ambient coordinates, expressed as actual matrix multiplication. -/
def embedMatrix {ι α : Type*} [Fintype α] [DecidableEq ι] (e : α → ι)
    (A : Matrix α α ℚ) : Matrix ι ι ℚ :=
  coordinateColumns e * A * (coordinateColumns e).transpose

 theorem embedMatrix_apply {ι α : Type*} [Fintype α] [DecidableEq ι] [DecidableEq α]
    (e : α → ι) (he : Function.Injective e) (A : Matrix α α ℚ) (a b : α) :
    embedMatrix e A (e a) (e b) = A a b := by
  simp [embedMatrix,Matrix.mul_apply,Matrix.transpose_apply,coordinateColumns,he.eq_iff]

 theorem embedMatrix_nonzero {ι α : Type*} [Fintype α] [DecidableEq ι]
    (e : α → ι) (A : Matrix α α ℚ) (i j : ι) (h : embedMatrix e A i j ≠ 0) :
    (∃ a, e a=i) ∧ (∃ b, e b=j) := by
  constructor
  · by_contra hn
    apply h
    simp only [embedMatrix,Matrix.mul_apply,Matrix.transpose_apply,coordinateColumns]
    apply Finset.sum_eq_zero
    intro b _
    have hi : ∀ a, i ≠ e a := by
      intro a ha
      exact hn ⟨a,ha.symm⟩
    simp only [if_neg (hi _),zero_mul,Finset.sum_const_zero]
  · by_contra hn
    apply h
    simp only [embedMatrix,Matrix.mul_apply,Matrix.transpose_apply,coordinateColumns]
    apply Finset.sum_eq_zero
    intro b _
    have hj : j ≠ e b := fun h => hn ⟨b,h.symm⟩
    simp only [if_neg hj,mul_zero]

 theorem embedMatrix_mul {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (e : α → ι) (he : Function.Injective e)
    (A B : Matrix α α ℚ) : embedMatrix e A * embedMatrix e B = embedMatrix e (A*B) := by
  unfold embedMatrix
  have hi := coordinateColumns_leftInverse e he
  calc
    coordinateColumns e * A * (coordinateColumns e).transpose *
      (coordinateColumns e * B * (coordinateColumns e).transpose) =
      coordinateColumns e * A * ((coordinateColumns e).transpose * coordinateColumns e) *
        B * (coordinateColumns e).transpose := by simp only [Matrix.mul_assoc]
    _ = coordinateColumns e * (A*B) * (coordinateColumns e).transpose := by rw [hi,Matrix.mul_one]; simp only [Matrix.mul_assoc]

 theorem embedMatrix_idempotent {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (e : α → ι) (he : Function.Injective e)
    (A : Matrix α α ℚ) (hA : A*A=A) : embedMatrix e A * embedMatrix e A = embedMatrix e A := by
  rw [embedMatrix_mul e he,hA]

end HiddenCircuits
