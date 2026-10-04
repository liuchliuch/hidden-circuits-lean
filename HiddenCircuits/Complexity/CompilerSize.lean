import HiddenCircuits.Complexity.NetworkSize

/-! Polynomial size of the actual count-preserving verifier-to-CNF image.
This theorem concerns size; it is deliberately not a running-time assertion. -/
namespace HiddenCircuits.Complexity
namespace VerifierTableau
open Polynomial TM2BooleanEncoding
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

noncomputable def heightPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  2*X+p+1+(horizonPolynomial M p)*C (TM2Space.machineBudget M.tm)

noncomputable def cellsPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  C (controlBits M.tm)+(heightPolynomial M p)*C (symbolBits M.tm)

noncomputable def formulaSizePolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  10*(p+(horizonPolynomial M p+1)*cellsPolynomial M p+1)*C (Fintype.card (Port M.tm)+3)*
    (2*cellsPolynomial M p+horizonPolynomial M p*cellsPolynomial M p*C (2^Fintype.card (Port M.tm))+2)
    +2*p+3

@[simp] theorem heightPolynomial_eval (p : Polynomial ℕ) (x : BitString) :
    (heightPolynomial M p).eval x.length = height M x (p.eval x.length) := by
  simp [heightPolynomial,height,horizonPolynomial_eval]

@[simp] theorem cellsPolynomial_eval (p : Polynomial ℕ) (x : BitString) :
    (cellsPolynomial M p).eval x.length = bitCount M.tm (height M x (p.eval x.length)) := by
  simp [cellsPolynomial,bitCount,heightPolynomial_eval]

theorem formulaSizePolynomial_eval (p : Polynomial ℕ) (x : BitString) :
    (formulaSizePolynomial M p).eval x.length =
      10*(p.eval x.length+(horizon M x (p.eval x.length)+1)*bitCount M.tm (height M x (p.eval x.length))+1)*
      (Fintype.card (Port M.tm)+3)*
      (2*bitCount M.tm (height M x (p.eval x.length))+
        horizon M x (p.eval x.length)*bitCount M.tm (height M x (p.eval x.length))*2^Fintype.card (Port M.tm)+2)
      +2*p.eval x.length+3 := by
  simp [formulaSizePolynomial,horizonPolynomial_eval,cellsPolynomial_eval,Polynomial.eval_finset_sum]

end VerifierTableau

theorem rejectingCNF_bits (n : ℕ) : (rejectingCNF n).bits.length = 2*n+3 := by
  simp [CNF.bits,rejectingCNF,CNF.clauseBits,encodeBitList]

namespace VerifierTableau
variable {v : BitString → Bool}
variable (M : Turing.TM2ComputableInPolyTime id Computability.encodeBool v)

theorem formula_polynomial_size (p : Polynomial ℕ) (x : BitString) :
    (CNFInput.encode (formula M x (p.eval x.length))).length ≤ (formulaSizePolynomial M p).eval x.length := by
  classical
  rw [formulaSizePolynomial_eval]
  by_cases ht : HasTrueSymbol M
  · rw [formula_pos M x _ ht]
    exact (positiveFormula_bits M x _ ht).trans (by omega)
  · rw [formula_neg M x _ ht]
    change (rejectingCNF (p.eval x.length)).bits.length ≤ _
    rw [rejectingCNF_bits]
    omega

end VerifierTableau

/-- A genuine #P verifier has a concrete count-preserving CNF family of polynomial
binary size. The uniform bit-operation running-time bridge remains separate. -/
theorem SharpP.exists_polynomial_size_cnf {f : BitString → ℕ} (hf : SharpP f) :
    ∃ (F : BitString → CNFInput) (q : Polynomial ℕ),
      (∀ x, (F x).2.2.satCount = f x) ∧
      (∀ x, (CNFInput.encode (F x)).length ≤ q.eval x.length) := by
  obtain ⟨p,v,⟨M⟩,hc⟩ := hf
  refine ⟨fun x => VerifierTableau.formula M x (p.eval x.length),
    VerifierTableau.formulaSizePolynomial M p,?_,?_⟩
  · intro x
    exact (VerifierTableau.formula_count M x _).trans (hc x).symm
  · exact VerifierTableau.formula_polynomial_size M p

end HiddenCircuits.Complexity
