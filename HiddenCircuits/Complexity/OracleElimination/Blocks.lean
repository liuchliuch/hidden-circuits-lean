import HiddenCircuits.Complexity.OracleElimination.Polynomial
import HiddenCircuits.Complexity.OracleBlocks

/-! Convenient operational interfaces for arbitrary polynomial-time oracle
blocks, including Boolean verifiers. No oracle-freedom assumption is needed. -/
namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

/-- A polynomial-time oracle block, possibly with dirty work tapes, becomes an
ordinary genuine TM2 computation when its target oracle is FP. -/
theorem polyTime_of_oracleBlock {f : BitString → BitString} {g : BitString → ℕ}
    (B : OracleBlock k) (p : Polynomial ℕ) (hg : FP g)
    (h : ∀ x,∃ s : Store k,∃ cost,
      B.Executes g (Function.update (fun _ => []) 0 x) s cost ∧
      s 0=f x ∧ cost ≤ p.eval x.length) : PolyTime f := by
  apply polyTime_of_oracle B.machine p hg
  intro x
  obtain ⟨s,t,hr,ho,hb⟩ := h x
  refine ⟨B.config B.exit s,t,?_,ho,hb⟩
  apply (OracleMachine.runs_iff_steps_halt B.machine).mpr
  exact ⟨hr,by simp [OracleMachine.step,machine,config,B.exit_halt]⟩

/-- Boolean-output form of general oracle elimination. -/
theorem polyVerifier_of_oracleBlock (v : BitString → Bool) {g : BitString → ℕ}
    (B : OracleBlock k) (p : Polynomial ℕ) (hg : FP g)
    (h : ∀ x,∃ s : Store k,∃ cost,
      B.Executes g (Function.update (fun _ => []) 0 x) s cost ∧
      s 0=Computability.encodeBool (v x) ∧ cost ≤ p.eval x.length) : PolyVerifier v := by
  obtain ⟨N⟩ := polyTime_of_oracleBlock B p hg h
  exact ⟨{ toTM2ComputableAux := N.toTM2ComputableAux,time := N.time,outputsFun := N.outputsFun }⟩

end HiddenCircuits.Complexity.OracleBlock
