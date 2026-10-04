import HiddenCircuits.Circuit.Runtime.SpectralWeightsProgram

/-! Each fixed required target is a true finite program from a single unary
input tape; the mode is supplied by a literal instruction, not by advice. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralWeightsProgram
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial
open SpectralWeights

noncomputable def forMode (mode : Bool) : OracleBlock 35 := seq (push 33 mode) program
noncomputable def unaryTime : Polynomial ℕ := time+3

 theorem forMode_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    ∃ t, (forMode mode).Executes oracle
      (Function.update (fun _ : Fin 36 => ([]:BitString)) 0 (List.replicate g true))
      (publicStore g mode (signedBits (denominator g)) (numeratorStream g mode)) t ∧ t≤unaryTime.eval g := by
  have hi : (push (33:Fin 36) mode).Executes oracle
      (Function.update (fun _ : Fin 36 => ([]:BitString)) 0 (List.replicate g true)) (publicStore g mode [] []) 1 := by
    convert push_executes oracle (33:Fin 36) mode
      (Function.update (fun _ : Fin 36 => ([]:BitString)) 0 (List.replicate g true)) using 1
    funext i;fin_cases i <;> simp [publicStore,state]
  obtain ⟨t,ht,hb⟩ := program_executes oracle g mode
  refine ⟨1+t+2,seq_executes _ _ oracle hi ht,?_⟩
  simp only [unaryTime,eval_add,eval_ofNat]
  omega

 theorem forMode_queryFree (mode : Bool) : (forMode mode).QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) program_queryFree

 theorem forMode_runs (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    ∃ c t, (forMode mode).machine.Runs oracle ((forMode mode).machine.init (List.replicate g true)) c t ∧
      c.stack=publicStore g mode (signedBits (denominator g)) (numeratorStream g mode) ∧ t≤unaryTime.eval g := by
  obtain ⟨t,ht,hb⟩ := forMode_executes oracle g mode
  refine ⟨(forMode mode).config (forMode mode).exit _,t,?_,rfl,hb⟩
  apply (OracleMachine.runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,(forMode mode).exit_halt]⟩
end HiddenCircuits.Circuit.Runtime.SpectralWeightsProgram
