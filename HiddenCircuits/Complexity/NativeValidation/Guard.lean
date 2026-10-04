import HiddenCircuits.Complexity.NativeValidation.Program
import HiddenCircuits.Complexity.RawValidationGuard

/-! Concrete native malformed-zero guards. The finite validator contracts are
fully discharged here; a caller supplies only its checked canonical solver. -/
namespace HiddenCircuits.Complexity.NativeValidation.Guard
open OracleBlock Polynomial RawValidationGuard
variable {k : ℕ}
noncomputable def constraintInput : InputProblem where
  Input:=ConstraintInput
  encode:=ConstraintInput.encode
  decode:=ConstraintInput.decode
  value C:=RationalOracleEncoding.code C.value
  decode_sound:=ConstraintInput.encode_of_decode
noncomputable def deltaInput : InputProblem where
  Input:=DeltaInput
  encode:=DeltaInput.encode
  decode:=DeltaInput.decode
  value C:=RationalOracleEncoding.code C.value
  decode_sound:=DeltaInput.encode_of_decode
lemma constraint_total : constraintInput.total=constraintProblem := by
  funext xs
  unfold InputProblem.total constraintProblem
  simp only [constraintInput]
  cases ConstraintInput.decode xs <;> rfl
lemma delta_total : deltaInput.total=deltaProblem := by
  funext xs
  unfold InputProblem.total deltaProblem
  simp only [deltaInput]
  cases DeltaInput.decode xs <;> rfl
lemma constraint_validator : ValidatorSpec constraintInput (Program.program false) Program.time := by
  intro g xs
  obtain ⟨c,hc,hb⟩:=Program.constraint_executes g xs
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> simp [EvalValidation.Finish.output,validationStore,marker,constraintInput]
lemma delta_validator : ValidatorSpec deltaInput (Program.program true) Program.time := by
  intro g xs
  obtain ⟨c,hc,hb⟩:=Program.delta_executes g xs
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext i;fin_cases i <;> simp [EvalValidation.Finish.output,validationStore,marker,deltaInput]
noncomputable def constraintProgram (S : OracleBlock k) : OracleBlock (k+31) := RawValidationGuard.program (Program.program false) S
noncomputable def deltaProgram (S : OracleBlock k) : OracleBlock (k+31) := RawValidationGuard.program (Program.program true) S
noncomputable def time (Q : Polynomial ℕ) : Polynomial ℕ := RawValidationGuard.time Program.time Q

theorem constraint_executes (S : OracleBlock k) (Q : Polynomial ℕ) (g : BitString→ℕ)
    (hS : SolverSpec constraintInput S Q g) (xs : BitString) :
    ∃c,(constraintProgram S).Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (constraintProblem xs))) c ∧ c≤(time Q).eval xs.length := by
  simpa only [constraint_total] using RawValidationGuard.program_executes constraintInput _ S _ Q constraint_validator g hS xs

theorem delta_executes (S : OracleBlock k) (Q : Polynomial ℕ) (g : BitString→ℕ)
    (hS : SolverSpec deltaInput S Q g) (xs : BitString) :
    ∃c,(deltaProgram S).Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (deltaProblem xs))) c ∧ c≤(time Q).eval xs.length := by
  simpa only [delta_total] using RawValidationGuard.program_executes deltaInput _ S _ Q delta_validator g hS xs

theorem constraint_reduction (S : OracleBlock k) (Q : Polynomial ℕ) (g : BitString→ℕ)
    (hS : SolverSpec constraintInput S Q g) : PolyTuringReduction constraintProblem g := by
  simpa only [constraint_total] using RawValidationGuard.reduction constraintInput _ S _ Q constraint_validator g hS

theorem delta_reduction (S : OracleBlock k) (Q : Polynomial ℕ) (g : BitString→ℕ)
    (hS : SolverSpec deltaInput S Q g) : PolyTuringReduction deltaProblem g := by
  simpa only [delta_total] using RawValidationGuard.reduction deltaInput _ S _ Q delta_validator g hS
end HiddenCircuits.Complexity.NativeValidation.Guard
