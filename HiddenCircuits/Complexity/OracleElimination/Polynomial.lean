import HiddenCircuits.Complexity.OracleElimination.Simulation

/-! Eliminate every polynomial-time oracle from a polynomially charged finite
stack program, in the original unrestricted finite-TM2 definition of FP. -/
namespace HiddenCircuits.Complexity.OracleElimination
open Polynomial
variable (M : OracleMachine) {g : BitString → ℕ}
variable (N : Turing.TM2ComputableInPolyTime id id (fun x => Computability.encodeNat (g x)))

/-- A polynomial obtained directly from the source runtime, the callee runtime,
and the proved copying/cleanup overhead. -/
noncomputable def simulationTime (p : Polynomial ℕ) : Polynomial ℕ :=
  p*(5*(X+p)+N.time.comp (X+p)+6)+C M.stackCount*(X+p+1)+2

 theorem simulationTime_eval (p : Polynomial ℕ) (n : ℕ) :
    (simulationTime M N p).eval n =
      p.eval n*allowance N (n+p.eval n)+M.stackCount*(n+p.eval n+1)+2 := by
  simp [simulationTime,allowance,eval_comp]

 theorem runtime_le (p : Polynomial ℕ) (n t : ℕ) (ht : t ≤ p.eval n) :
    t*allowance N (n+t)+M.stackCount*(n+t+1)+2 ≤ (simulationTime M N p).eval n := by
  rw [simulationTime_eval]
  have hA := allowance_mono N (Nat.add_le_add_left ht n)
  have h1 := Nat.mul_le_mul ht hA
  have h2 := Nat.mul_le_mul_left M.stackCount (show n+t+1 ≤ n+p.eval n+1 by omega)
  omega

/-- This construction accepts the actual source execution theorem and an
arbitrary genuine TM2 callee, with no assumed closure or simulation certificate. -/
noncomputable def computableOfOracle {f : BitString → BitString} (p : Polynomial ℕ)
    (h : ∀ x,∃ c : M.Config,∃ t, M.Runs g (M.init x) c t ∧
      c.stack M.output=f x ∧ t ≤ p.eval x.length) :
    Turing.TM2ComputableInPolyTime id id f where
  tm := machine M N
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := simulationTime M N p
  outputsFun x := by
    apply Classical.choice
    obtain ⟨c,t,hr,ho,hb⟩ := h x
    have he := (runs_to_output M N hr).mono (runtime_le M N p x.length t hb)
    rw [ho] at he
    simpa [Eval,Turing.TM2OutputsInTime,Equiv.refl] using he

end HiddenCircuits.Complexity.OracleElimination

namespace HiddenCircuits.Complexity

/-- General bit-string oracle elimination, reusable for verifier constructions. -/
theorem polyTime_of_oracle {f : BitString → BitString} {g : BitString → ℕ}
    (M : OracleMachine) (p : Polynomial ℕ) (hg : FP g)
    (h : ∀ x,∃ c : M.Config,∃ t, M.Runs g (M.init x) c t ∧
      c.stack M.output=f x ∧ t ≤ p.eval x.length) : PolyTime f := by
  obtain ⟨N⟩ := hg
  exact ⟨OracleElimination.computableOfOracle M N p h⟩

/-- A polynomial-time target oracle can be eliminated from every charged
polynomial-time Turing reduction. -/
theorem PolyTuringReduction.fp {f g : BitString → ℕ}
    (h : PolyTuringReduction f g) (hg : FP g) : FP f := by
  obtain ⟨M,p,h⟩ := h
  exact polyTime_of_oracle M p hg h

/-- Every #P function becomes FP if a #P-hard target is FP. The reverse
containment, required for literal class equality, is a separate theorem. -/
theorem SharpPHard.sharpP_subset_fp {g : BitString → ℕ} (h : SharpPHard g) (hg : FP g) :
    ∀ f : BitString → ℕ,SharpP f → FP f :=
  fun f hf => (h f hf).fp hg

/-- A separation witness rules out every polynomial-time algorithm for a
#P-hard target, with no restriction to a selected stack-language compiler. -/
theorem SharpPHard.not_fp_of_separation {g : BitString → ℕ} (h : SharpPHard g)
    (hsep : ¬∀ f : BitString → ℕ, SharpP f → FP f) : ¬FP g :=
  fun hg => hsep (h.sharpP_subset_fp hg)

end HiddenCircuits.Complexity
