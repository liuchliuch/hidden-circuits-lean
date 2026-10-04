import HiddenCircuits.Complexity.SharpP

/-! Elementary monotonicity used to assemble explicit operational time bounds. -/
namespace HiddenCircuits.Complexity

theorem polynomial_nat_eval_mono (p : Polynomial ℕ) : Monotone (fun n => p.eval n) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x y h
    simpa using Nat.add_le_add (hp h) (hq h)
  | monomial n a =>
    intro x y h
    simpa [Polynomial.eval_monomial] using Nat.mul_le_mul_left a (Nat.pow_le_pow_left h n)

end HiddenCircuits.Complexity
