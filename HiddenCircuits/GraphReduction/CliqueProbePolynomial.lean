import HiddenCircuits.GraphReduction.CliqueProbeCount

/-! The one shared size polynomial for actual simple unweighted clique probes. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
open Polynomial
variable {V I : Type*} [Fintype V] [Fintype I]

/-- Every summand records disjoint even original color classes and the actual residual graph count. -/
noncomputable def cliqueProbePolynomial (G : SimpleGraph V) (A : I → V → Prop) : ℚ[X] :=
  ∑ c : EvenCliqueColors A,
    C (perfectMatchingCount (G.induce {v | c.val.val v=none}) : ℚ) *
      ∏ i, cliqueProbeFactor (cliqueHalf c i)

 theorem cliqueProbePolynomial_even (G : SimpleGraph V) (A : I → V → Prop) (t : ℕ) :
    (cliqueProbePolynomial G A).eval (2*t : ℚ) =
      (∑ c : EvenCliqueColors A, perfectMatchingCount (G.induce {v | c.val.val v=none}) *
        ∏ i, 2^(cliqueHalf c i) * t.descFactorial (cliqueHalf c i) : ℕ) := by
  classical
  simp [cliqueProbePolynomial,Polynomial.eval_finset_sum,Polynomial.eval_prod,
    cliqueProbeFactor_even,Nat.cast_sum,Nat.cast_prod]

/-- Exact normalization for every nonnegative even sample, including all insufficient sizes. -/
theorem cliqueProbePolynomial_count (G : SimpleGraph V) (A : I → V → Prop) (t : ℕ) :
    (cliqueProbePolynomial G A).eval (2*t : ℚ) =
      (perfectMatchingCount (cliqueProbeGraph G A (2*t)) : ℚ) /
        (oddFactorial t : ℚ)^Fintype.card I := by
  rw [cliqueProbeGraph_count,Nat.cast_mul,Nat.cast_pow,cliqueProbePolynomial_even]
  exact (mul_div_cancel_right₀ _ (pow_ne_zero _ (by exact_mod_cast (oddFactorial_pos t).ne'))).symm

/-- Each degree-a factor consumes 2a distinct original vertices. -/
theorem cliqueProbePolynomial_degree (G : SimpleGraph V) (A : I → V → Prop) :
    (cliqueProbePolynomial G A).natDegree ≤ Fintype.card V/2 := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro c _
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_prod_le ..).trans
  exact (Finset.sum_le_sum (fun i _ => cliqueProbeFactor_degree (cliqueHalf c i))).trans
    (cliqueHalf_sum_le c)

/-- Negative evaluation is exactly the sum of negatively weighted clique matching blocks. -/
theorem cliqueProbePolynomial_negative (G : SimpleGraph V) (A : I → V → Prop) :
    (cliqueProbePolynomial G A).eval (-1) =
      ∑ c : EvenCliqueColors A, (perfectMatchingCount (G.induce {v | c.val.val v=none}) : ℚ) *
        ∏ i, (-1 : ℚ)^(cliqueHalf c i) * (oddFactorial (cliqueHalf c i) : ℚ) := by
  classical
  simp only [cliqueProbePolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,cliqueProbeFactor_negative]

end HiddenCircuits.GraphReduction
