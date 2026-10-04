import HiddenCircuits.GraphReduction.CliqueMatchingCount
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! The even-sample clique-probe factor, with small samples handled exactly. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
open Polynomial

 theorem oddFactorial_pos (a : ℕ) : 0<oddFactorial a := by
  unfold oddFactorial
  apply Finset.prod_pos
  intro j _
  omega

/-- Separate the even and odd factors in an ordinary factorial. -/
theorem factorial_even_split (t : ℕ) : (2*t).factorial = 2^t * t.factorial * oddFactorial t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2*(t+1)=(2*t+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ,
      ih,pow_succ,Nat.factorial_succ,oddFactorial_succ]
    ring

/-- Normalization of one clique-probe extension; both sides vanish if 2t<2a. -/
theorem cliqueProbe_factor_nat (t a : ℕ) :
    (2*t).descFactorial (2*a) * oddFactorial (t-a) =
      oddFactorial t * 2^a * t.descFactorial a := by
  by_cases ha : a≤t
  · have h2 := Nat.factorial_mul_descFactorial (show 2*a≤2*t by omega)
    have ht := Nat.factorial_mul_descFactorial ha
    rw [show 2*t-2*a=2*(t-a) by omega,factorial_even_split,factorial_even_split] at h2
    have hp : 2^t=2^a*2^(t-a) := by rw [← pow_add]; congr 1; omega
    rw [hp,← ht] at h2
    apply Nat.mul_right_cancel (show 0<2^(t-a)*(t-a).factorial by positivity)
    nlinarith only [h2]
  · have hta : t<a := by omega
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (show 2*t<2*a by omega),
      Nat.descFactorial_eq_zero_iff_lt.mpr hta]
    simp

/-- f_a(s)=∏_{j<a}(s−2j), with the common indeterminate shared by every probe. -/
noncomputable def cliqueProbeFactor (a : ℕ) : ℚ[X] := ∏ j ∈ Finset.range a, (X-C (2*j : ℚ))

@[simp] theorem cliqueProbeFactor_zero : cliqueProbeFactor 0=1 := by simp [cliqueProbeFactor]

 theorem cliqueProbeFactor_succ (a : ℕ) :
    cliqueProbeFactor (a+1)=cliqueProbeFactor a * (X-C (2*a : ℚ)) := by
  simp only [cliqueProbeFactor,Finset.prod_range_succ]

 theorem cliqueProbeFactor_degree (a : ℕ) : (cliqueProbeFactor a).natDegree≤a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [cliqueProbeFactor_succ]
    have hc : (X-C (2*a : ℚ)).natDegree=1 := Polynomial.natDegree_X_sub_C _
    exact (Polynomial.natDegree_mul_le ..).trans (Nat.add_le_add ih hc.le)

 theorem cliqueProbeFactor_even (a t : ℕ) :
    (cliqueProbeFactor a).eval (2*t : ℚ) = (2 : ℚ)^a * (t.descFactorial a : ℚ) := by
  rw [← descPochhammer_eval_eq_descFactorial ℚ t a,descPochhammer_eval_eq_prod_range]
  unfold cliqueProbeFactor
  rw [Polynomial.eval_prod]
  calc
    ∏ j ∈ Finset.range a, (X-C (2*j : ℚ)).eval (2*t) =
        ∏ j ∈ Finset.range a, (2 : ℚ)*((t : ℚ)-(j : ℚ)) := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

 theorem cliqueProbeFactor_negative (a : ℕ) :
    (cliqueProbeFactor a).eval (-1) = (-1 : ℚ)^a * (oddFactorial a : ℚ) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [cliqueProbeFactor_succ,Polynomial.eval_mul,ih,pow_succ,oddFactorial_succ]
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,Nat.cast_mul,
      Nat.cast_add,Nat.cast_ofNat]
    ring

end HiddenCircuits.GraphReduction
