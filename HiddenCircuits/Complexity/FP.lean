import HiddenCircuits.Complexity.OracleMachine
import HiddenCircuits.Complexity.TM2Space
import HiddenCircuits.Complexity.PolynomialBounds

/-! Natural-valued deterministic polynomial time in exactly the finite TM2
model used to define `SharpP`. This definition does not restrict the solver to
any particular compiler's image. -/
namespace HiddenCircuits.Complexity

/-- Natural-valued FP, with ordinary binary output and the existing TM2 model. -/
def FP (f : BitString → ℕ) : Prop :=
  PolyTime (fun x => Computability.encodeNat (f x))

/-- The literal equality of natural-valued FP and the verifier counting class. -/
def FP_eq_SharpP : Prop := ∀ f : BitString → ℕ, FP f ↔ SharpP f

/-- Polynomial-time finite TM2 computations have polynomially bounded output.
The constant is derived from the actual finite statement syntax. -/
theorem PolyTime.output_length_bound {f : BitString → BitString} (hf : PolyTime f) :
    ∃ p : Polynomial ℕ, ∀ x, (f x).length ≤ p.eval x.length := by
  obtain ⟨M⟩ := hf
  refine ⟨Polynomial.X + M.time * Polynomial.C (TM2Space.machineBudget M.tm), fun x => ?_⟩
  have h := TM2Space.input_tableau_stack_bound M.tm
    (x.map M.inputAlphabet.invFun) (M.time.eval x.length) M.tm.k₁
  have he := tm2_stutter_output M.tm _ _ _ (M.outputsFun x)
  simp only [id_eq] at he
  rw [he] at h
  simpa [Turing.haltList] using h

/-- Binary output balance is a theorem of FP, not a promise on an oracle. -/
theorem FP.binary_output_bound {f : BitString → ℕ} (hf : FP f) :
    ∃ p : Polynomial ℕ, ∀ x, (Computability.encodeNat (f x)).length ≤ p.eval x.length :=
  PolyTime.output_length_bound hf

/-- An FP function is eligible for the charged model's reflexive reduction. -/
theorem FP.reduces_to_self {f : BitString → ℕ} (hf : FP f) : PolyTuringReduction f f :=
  polyTuringReduction_refl hf.binary_output_bound

end HiddenCircuits.Complexity
