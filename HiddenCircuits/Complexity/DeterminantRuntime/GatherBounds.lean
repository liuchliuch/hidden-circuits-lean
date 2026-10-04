import HiddenCircuits.Complexity.DeterminantRuntime.Gather
import HiddenCircuits.Complexity.PolynomialBounds

/-! Closed natural-polynomial envelope for the charged word-gather routine. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Gather
open Polynomial

noncomputable def timePolynomial : Polynomial ℕ :=
  5*X+5*X+
  X*(5*X+5*(X+X*X)+(X+X*X+1)*(6*X+14)+9+6*X+5*X+15)+
  X+X*X+4*X*(X+1)+20

theorem timeBound_le_eval (L start stride count N : ℕ)
    (hL : L ≤ N) (hs : start ≤ N) (hd : stride ≤ N) (hc : count ≤ N) :
    timeBound L start stride count ≤ timePolynomial.eval N := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  unfold timeBound GraphReduction.Runtime.lookupBound
  gcongr

end HiddenCircuits.Complexity.DeterminantRuntime.Gather
