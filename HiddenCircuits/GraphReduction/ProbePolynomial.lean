import HiddenCircuits.GraphReduction.ProbeCount
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! One shared probe-size polynomial and exact factorial normalization. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
open Polynomial
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

/-- The unique-extension sum uses one indeterminate shared by all probe pairs. -/
noncomputable def probePolynomial (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    ℚ[X] :=
  ∑ cd : BalancedColors A B,
    C (Fintype.card (OriginalResidual R cd.val.val) : ℚ) *
      ∏ i, descPochhammer ℚ (Fintype.card (OriginalFiber cd.val.val.1 (some i)))

 theorem probePolynomial_nat (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) (s : ℕ) :
    (probePolynomial R A B).eval (s : ℚ) =
      (∑ cd : BalancedColors A B, Fintype.card (OriginalResidual R cd.val.val) *
        ∏ i, s.descFactorial (Fintype.card (OriginalFiber cd.val.val.1 (some i)))) := by
  classical
  simp [probePolynomial,Polynomial.eval_finset_sum,Polynomial.eval_prod,
    descPochhammer_eval_eq_descFactorial,Nat.cast_sum,Nat.cast_prod]

/-- The stated normalized oracle sample identity, valid for every nonnegative size. -/
theorem probePolynomial_count (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) (s : ℕ) :
    (probePolynomial R A B).eval (s : ℚ) =
      (perfectMatchingCount (probeGraph R A B s) : ℚ) /
        (s.factorial : ℚ) ^ Fintype.card I := by
  rw [probeGraph_count,Nat.cast_mul,Nat.cast_pow,probePolynomial_nat]
  exact (mul_div_cancel_right₀ _ (pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero s))).symm

/-- Each original vertex appears in at most one probe factor. -/
theorem probePolynomial_degree (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    (probePolynomial R A B).natDegree ≤ Fintype.card X := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro cd _
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_prod_le ..).trans
  simpa only [descPochhammer_natDegree] using assigned_card_le cd.val.val.1

/-- At the formal negative sample, one local factor counts all negatively weighted bijections. -/
theorem descPochhammer_neg_one (a : ℕ) :
    (descPochhammer ℚ a).eval (-1) = (-1 : ℚ)^a * (a.factorial : ℚ) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [descPochhammer_succ_right,Polynomial.eval_mul,ih]
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_natCast,
      pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

/-- The formal negative evaluation is postprocessing only: every sample graph is still unweighted. -/
theorem probePolynomial_neg_one (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    (probePolynomial R A B).eval (-1) =
      ∑ cd : BalancedColors A B, (Fintype.card (OriginalResidual R cd.val.val) : ℚ) *
        ∏ i, (-1 : ℚ)^(Fintype.card (OriginalFiber cd.val.val.1 (some i))) *
          ((Fintype.card (OriginalFiber cd.val.val.1 (some i))).factorial : ℚ) := by
  classical
  simp only [probePolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,descPochhammer_neg_one]

end HiddenCircuits.GraphReduction
