import HiddenCircuits.Transfers

namespace HiddenCircuits
open scoped BigOperators

/-- Exact integer-valuedness inside ℚ, used to avoid introducing fractional oracle answers. -/
def IsInteger (x : ℚ) : Prop := ∃ z : ℤ, x = (z : ℚ)

namespace IsInteger
@[simp] theorem zero : IsInteger 0 := ⟨0, by simp⟩
@[simp] theorem one : IsInteger 1 := ⟨1, by simp⟩
 theorem add {x y : ℚ} (hx : IsInteger x) (hy : IsInteger y) : IsInteger (x+y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b, by simp⟩
 theorem mul {x y : ℚ} (hx : IsInteger x) (hy : IsInteger y) : IsInteger (x*y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a*b, by simp⟩
 theorem neg {x : ℚ} (hx : IsInteger x) : IsInteger (-x) := by
  obtain ⟨a,rfl⟩ := hx; exact ⟨-a, by simp⟩
 theorem sub {x y : ℚ} (hx : IsInteger x) (hy : IsInteger y) : IsInteger (x-y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg
 theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, IsInteger (f i)) : IsInteger (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
 theorem prod {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, IsInteger (f i)) : IsInteger (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
end IsInteger

def IntegralMatrix {ι κ : Type*} (M : Matrix ι κ ℚ) : Prop := ∀ i j, IsInteger (M i j)

namespace IntegralMatrix
variable {ι κ ν : Type*}
 theorem one [DecidableEq ι] : IntegralMatrix (1 : Matrix ι ι ℚ) := by
  intro i j
  by_cases h : i=j <;> simp [Matrix.one_apply, h, IsInteger.zero, IsInteger.one]
 theorem mul [Fintype κ] {A : Matrix ι κ ℚ} {B : Matrix κ ν ℚ}
    (hA : IntegralMatrix A) (hB : IntegralMatrix B) : IntegralMatrix (A*B) := by
  intro i j
  exact IsInteger.sum _ _ (fun k _ => (hA i k).mul (hB k j))
 theorem neg {A : Matrix ι κ ℚ} (hA : IntegralMatrix A) : IntegralMatrix (-A) :=
  fun i j => (hA i j).neg
 theorem sub {A B : Matrix ι κ ℚ} (hA : IntegralMatrix A) (hB : IntegralMatrix B) :
    IntegralMatrix (A-B) := fun i j => (hA i j).sub (hB i j)
 theorem pow [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℚ} (hA : IntegralMatrix A) :
    ∀ k, IntegralMatrix (A^k)
  | 0 => by simpa using one
  | k+1 => by rw [pow_succ]; exact (pow hA k).mul hA
 theorem sum {α : Type*} (s : Finset α) (A : α → Matrix ι κ ℚ)
    (hA : ∀ k ∈ s, IntegralMatrix (A k)) : IntegralMatrix (∑ k ∈ s, A k) := by
  intro i j
  simp only [Matrix.sum_apply]
  exact IsInteger.sum _ _ (fun k hk => hA k hk i j)
end IntegralMatrix

 theorem compound_integral {n q : ℕ} {M : Matrix (Fin n) (Fin n) ℚ}
    (hM : IntegralMatrix M) : IntegralMatrix (compound (q:=q) M) := by
  intro S T
  apply IsInteger.sum
  intro σ _
  exact IsInteger.prod _ _ (fun j _ => hM (S.track (σ j)) (T.track j))

 theorem upper_integral (n : ℕ) : IntegralMatrix (upper n) := by
  intro i j
  unfold upper
  split_ifs <;> simp

 theorem upperInverse_integral (n q : ℕ) : IntegralMatrix (upperInverse n q) := by
  unfold upperInverse inverseSeries
  apply IntegralMatrix.sum
  intro k _
  exact ((compound_integral (upper_integral n)).sub IntegralMatrix.one).neg.pow k

 theorem rise_integral (n q : ℕ) (i : Fin (n-1)) : IntegralMatrix (rise n q i) := by
  apply IntegralMatrix.mul _ (upperInverse_integral n q)
  apply compound_integral
  intro a b
  unfold addedCut
  split_ifs
  · exact IsInteger.one
  · exact upper_integral n a b

 theorem drop_integral (n q : ℕ) (i : Fin (n-1)) : IntegralMatrix (drop n q i) := by
  apply IntegralMatrix.mul _ (upperInverse_integral n q)
  apply compound_integral
  intro a b
  unfold deletedCut
  split_ifs
  · exact IsInteger.zero
  · exact upper_integral n a b

 theorem letter_integral {n : ℕ} (q : ℕ) (l : Letter n) : IntegralMatrix (l.matrix q) := by
  cases l with
  | mk kind i =>
    cases kind with
    | R => exact rise_integral n q i
    | D => exact drop_integral n q i
    | B => exact fun S T => rise_integral n (n-q) i T.complement S.complement
    | E => exact fun S T => drop_integral n (n-q) i T.complement S.complement

 theorem word_integral {n : ℕ} (q : ℕ) (w : List (Letter n)) : IntegralMatrix (wordMatrix q w) := by
  induction w with
  | nil => exact IntegralMatrix.one
  | cons l w ih => exact (letter_integral q l).mul ih

/-- The integer-valuedness conclusion of Lemma 3.2, with the concrete WordEval input. -/
theorem WordInstance.value_integral (w : WordInstance) : IsInteger w.value :=
  word_integral w.particles w.word w.source w.target

end HiddenCircuits
