import HiddenCircuits.Complexity.UnaryPolynomial

/-! Executable polynomial clocks and fair-tape budgets.
Path-dependent correctness is proved in PartnerBudgetCorrectness. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerBudget
open Polynomial
attribute [local instance] Classical.propDecidable

noncomputable def lengthPolynomial : Polynomial ℕ := X*(X*(8*X*X+4))
noncomputable def trafficPolynomial : Polynomial ℕ := lengthPolynomial*((X+1)^30*X^30*X^30*X*X)
noncomputable def stepsPolynomial : Polynomial ℕ :=
  2*(lengthPolynomial+1)*(8*(X+1)^2)*(trafficPolynomial+1)*(X^2+2*X)
noncomputable def bitsPolynomial : Polynomial ℕ := (1+2*X)*stepsPolynomial

def length (n : ℕ) : ℕ := n*(n*(8*n*n+4))
def traffic (n : ℕ) : ℕ := length n*((n+1)^30*n^30*n^30*n*n)

def steps (N : ℕ) : ℕ := 2*(length N+1)*(8*(N+1)^2)*(traffic N+1)*(N^2+2*N)
def bits (N : ℕ) : ℕ := (1+2*N)*steps N

lemma length_eval (N : ℕ) : lengthPolynomial.eval N=length N := by
  simp [lengthPolynomial,length]
lemma traffic_eval (N : ℕ) : trafficPolynomial.eval N=traffic N := by
  simp [trafficPolynomial,traffic,length_eval]
@[simp] lemma steps_eval (N : ℕ) : stepsPolynomial.eval N=steps N := by
  simp [stepsPolynomial,steps,length_eval,traffic_eval]
@[simp] lemma bits_eval (N : ℕ) : bitsPolynomial.eval N=bits N := by simp [bitsPolynomial,bits]

lemma length_mono {n N : ℕ} (h : n≤N) : length n≤length N := by
  unfold length;gcongr
lemma traffic_mono {n N : ℕ} (h : n≤N) : traffic n≤traffic N := by
  unfold traffic
  apply Nat.mul_le_mul (length_mono h)
  gcongr

lemma tape_budget {n N : ℕ} (hn : n≤N) : (1+(Nat.size n+Nat.size n))*steps N≤bits N := by
  unfold bits
  apply Nat.mul_le_mul_right
  have hh : Nat.size n≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega

end HiddenCircuits.Approximation.SamplerRuntime.PartnerBudget
