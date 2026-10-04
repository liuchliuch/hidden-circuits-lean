import HiddenCircuits.PairedUnipotent
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Sum

namespace HiddenCircuits
noncomputable section
open scoped BigOperators
open Polynomial

/-- The rational falling-binomial polynomial, including the negative interpolation point. -/
def binomialPolynomial (j : ℕ) : ℚ[X] := ((j.factorial : ℚ)⁻¹) • descPochhammer ℚ j

 theorem binomialPolynomial_degree (j : ℕ) : (binomialPolynomial j).natDegree≤j := by
  exact (Polynomial.natDegree_smul_le _ _).trans_eq (descPochhammer_natDegree ℚ j)

@[simp] theorem binomialPolynomial_nat (j t : ℕ) :
    (binomialPolynomial j).eval (t:ℚ) = t.choose j := by
  rw [binomialPolynomial,Polynomial.eval_smul,descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,smul_eq_mul]
  have hf : (j.factorial : ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [← mul_assoc,inv_mul_cancel₀ hf,one_mul]

 theorem descPochhammer_neg_one (j : ℕ) :
    (descPochhammer ℚ j).eval (-1) = (-1:ℚ)^j * j.factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [descPochhammer_succ_eval,ih,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
    ring

@[simp] theorem binomialPolynomial_neg_one (j : ℕ) :
    (binomialPolynomial j).eval (-1)=(-1:ℚ)^j := by
  rw [binomialPolynomial,Polynomial.eval_smul,descPochhammer_neg_one,smul_eq_mul]
  have hf : (j.factorial:ℚ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix entries as constant rational polynomials. -/
def constantMatrix (M : Matrix ι ι ℚ) : Matrix ι ι ℚ[X] := fun i j => C (M i j)

/-- Entrywise evaluation of an actual polynomial matrix. -/
def evaluateMatrix (t : ℚ) (M : Matrix ι ι ℚ[X]) : Matrix ι ι ℚ := fun i j => (M i j).eval t

@[simp] theorem evaluateMatrix_constant (t : ℚ) (M : Matrix ι ι ℚ) :
    evaluateMatrix t (constantMatrix M)=M := by ext; simp [evaluateMatrix,constantMatrix]

@[simp] theorem evaluateMatrix_one (t : ℚ) : evaluateMatrix t (1 : Matrix ι ι ℚ[X])=1 := by
  ext i j
  by_cases h:i=j <;> simp [evaluateMatrix,Matrix.one_apply,h]

@[simp] theorem evaluateMatrix_mul (t : ℚ) (M N : Matrix ι ι ℚ[X]) :
    evaluateMatrix t (M*N)=evaluateMatrix t M * evaluateMatrix t N := by
  ext i j
  simp [evaluateMatrix,Matrix.mul_apply,Polynomial.eval_finset_sum]

/-- Polynomially parameterized power of a nilpotent perturbation, degree at most d. -/
def unipotentPolynomial (K : Matrix ι ι ℚ) (d : ℕ) : Matrix ι ι ℚ[X] :=
  fun i j => ∑ a ∈ Finset.range (d+1), binomialPolynomial a * C ((K^a) i j)

 theorem unipotentPolynomial_degree (K : Matrix ι ι ℚ) (d : ℕ) (i j : ι) :
    (unipotentPolynomial K d i j).natDegree≤d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  have hd : a≤d := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  exact (Polynomial.natDegree_mul_C_le _ _).trans ((binomialPolynomial_degree a).trans hd)

 theorem unipotentPolynomial_evaluate (K : Matrix ι ι ℚ) (d : ℕ) (t : ℚ) :
    evaluateMatrix t (unipotentPolynomial K d) =
      ∑ a ∈ Finset.range (d+1), ((binomialPolynomial a).eval t) • K^a := by
  ext i j
  simp [unipotentPolynomial,evaluateMatrix,Matrix.sum_apply,Polynomial.eval_finset_sum]

 theorem matrix_mul_natCast (M : Matrix ι ι ℚ) (n : ℕ) : M * (n : Matrix ι ι ℚ)=(n:ℚ) • M := by
  ext i j
  simp [Matrix.mul_apply,Matrix.natCast_apply,mul_comm]

 theorem binomial_matrix_power (K : Matrix ι ι ℚ) (t : ℕ) :
    (1+K)^t=∑ a ∈ Finset.range (t+1), (t.choose a:ℚ) • K^a := by
  have h := (Commute.one_right K).add_pow t
  simpa only [add_comm K 1,one_pow,mul_one,matrix_mul_natCast] using h

/-- The truncated polynomial agrees with every nonnegative integer power, even beyond its degree. -/
theorem unipotentPolynomial_nat (K : Matrix ι ι ℚ) (d : ℕ) (hK : K^(d+1)=0) (t : ℕ) :
    evaluateMatrix (t:ℚ) (unipotentPolynomial K d)=(1+K)^t := by
  rw [unipotentPolynomial_evaluate,binomial_matrix_power]
  simp only [binomialPolynomial_nat]
  by_cases htd:t≤d
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro a ha hat
    have ht : t<a := by simp only [Finset.mem_range] at ha hat; omega
    simp [Nat.choose_eq_zero_of_lt ht]
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro a ha had
    have hd : d+1≤a := by simp only [Finset.mem_range] at ha had; omega
    rw [pow_eq_zero_of_le hd hK,smul_zero]

/-- Negative evaluation is the finite inverse series, never a weighted sampled graph. -/
theorem unipotentPolynomial_neg_one (K : Matrix ι ι ℚ) (d : ℕ) :
    evaluateMatrix (-1) (unipotentPolynomial K d)=inverseSeries K d := by
  rw [unipotentPolynomial_evaluate]
  unfold inverseSeries
  apply Finset.sum_congr rfl
  intro a _
  rw [binomialPolynomial_neg_one,← smul_pow,neg_one_smul]

end Matrix
end
end HiddenCircuits
