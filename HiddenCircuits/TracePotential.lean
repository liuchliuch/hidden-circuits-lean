import HiddenCircuits.MatrixEmbedding
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HiddenCircuits
open scoped BigOperators
section
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Weak monotonicity of an integer potential passes to every actual matrix power. -/
theorem nondecreasing_potential_pow (M : Matrix ι ι R) (ω : ι → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → ω i ≤ ω j) :
    ∀ m i j, (M^m) i j ≠ 0 → ω i ≤ ω j := by
  intro m
  induction m with
  | zero =>
    intro i j h
    by_cases he:i=j
    · subst j; rfl
    · exact False.elim (h (by simp [he]))
  | succ m ih =>
    intro i j h
    rw [pow_succ,Matrix.mul_apply] at h
    obtain ⟨z,_,hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (ih i z (fun hh => hz (by rw [hh,zero_mul]))).trans
      (hM z j (fun hh => hz (by rw [hh,mul_zero])))

/-- Equal-potential blocks of powers depend only on equal-potential blocks of the base matrix. -/
theorem potential_pow_equal_level (M D : Matrix ι ι R) (ω : ι → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → ω i ≤ ω j)
    (hD : ∀ i j, D i j ≠ 0 → ω i ≤ ω j)
    (heq : ∀ i j, ω i=ω j → M i j=D i j) :
    ∀ m i j, ω i=ω j → (M^m) i j=(D^m) i j := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro i j hij
    rw [pow_succ,pow_succ,Matrix.mul_apply,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz:ω i=ω z
    · rw [ih i z hz,heq z j (hz.symm.trans hij)]
    · have hm : (M^m) i z * M z j=0 := by
        by_contra hn
        have h1 := nondecreasing_potential_pow M ω hM m i z (fun h => hn (by rw [h,zero_mul]))
        have h2 := hM z j (fun h => hn (by rw [h,mul_zero]))
        omega
      have hd : (D^m) i z * D z j=0 := by
        by_contra hn
        have h1 := nondecreasing_potential_pow D ω hD m i z (fun h => hn (by rw [h,zero_mul]))
        have h2 := hD z j (fun h => hn (by rw [h,mul_zero]))
        omega
      rw [hm,hd]

 theorem potential_pow_trace (M D : Matrix ι ι R) (ω : ι → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → ω i ≤ ω j)
    (hD : ∀ i j, D i j ≠ 0 → ω i ≤ ω j)
    (heq : ∀ i j, ω i=ω j → M i j=D i j) (m : ℕ) :
    (M^m).trace=(D^m).trace := by
  apply Finset.sum_congr rfl
  intro i _
  exact potential_pow_equal_level M D ω hM hD heq m i i rfl
end

 theorem embedMatrix_trace {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (e : α → ι) (he : Function.Injective e)
    (A : Matrix α α ℚ) : (embedMatrix e A).trace=A.trace := by
  unfold embedMatrix
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc,coordinateColumns_leftInverse e he,Matrix.one_mul]

end HiddenCircuits
