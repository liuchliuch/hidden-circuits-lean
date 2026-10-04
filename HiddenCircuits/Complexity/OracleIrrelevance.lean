import HiddenCircuits.Complexity.OracleBlockLift

/-! Changing the oracle has no effect on an actual syntactically query-free
program. The result follows instruction by instruction with identical charge. -/
namespace HiddenCircuits.Complexity.OracleMachine

lemma step_oracle_eq (M : OracleMachine) (hq : M.QueryFree) (g h : BitString → ℕ) (c : M.Config) :
    M.step g c=M.step h c := by
  cases hc : M.code c.pc with
  | halt => simp [step,hc]
  | jump next => simp [step,hc]
  | push s b next => simp [step,hc]
  | pop s e z o => simp [step,hc]
  | query i o next => exact False.elim (hq c.pc i o next hc)

theorem Steps.changeOracle {M : OracleMachine} (hq : M.QueryFree) {g : BitString → ℕ}
    (h : BitString → ℕ) {c d : M.Config} {t : ℕ} (run : M.Steps g c d t) : M.Steps h c d t := by
  induction run with
  | refl c => exact Steps.refl c
  | next step tail ih =>
    apply Steps.next _ ih
    rw [←step_oracle_eq M hq g h]
    exact step

end HiddenCircuits.Complexity.OracleMachine

namespace HiddenCircuits.Complexity.OracleBlock
variable {k : ℕ}

theorem Executes.changeOracle {B : OracleBlock k} (hq : B.QueryFree) {g : BitString → ℕ}
    (h : BitString → ℕ) {s t : Store k} {cost : ℕ} (run : B.Executes g s t cost) : B.Executes h s t cost :=
  OracleMachine.Steps.changeOracle hq h run

end HiddenCircuits.Complexity.OracleBlock
