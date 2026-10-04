import HiddenCircuits.Circuit.Runtime.SpectralConstraintFinish
import HiddenCircuits.Circuit.Runtime.SpectralDeltaDriverRuntime
import HiddenCircuits.Circuit.Runtime.ConstraintZeroModel

/-! Independent N/CZ→Delta evaluation: literal input metadata, two physical
spectral loops, ratio cleanup and actual canonical rational normalization. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralConstraint
open Complexity OracleBlock BinaryArithmetic Polynomial

noncomputable def metadata : OracleBlock 67:=SpectralDeltaDriver.lift ConstraintZero.metadata
noncomputable def core : OracleBlock 67:=seq metadata SpectralDeltaDriver.program
noncomputable def coreTime : Polynomial ℕ:=CircuitMetadata.time+SpectralDeltaDriver.time.comp (X+CircuitMetadata.time)+2
noncomputable def program : OracleBlock 67:=seq core finish
noncomputable def time : Polynomial ℕ:=coreTime+timeFinish.comp (X+coreTime)+2

lemma metadata_executes (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) :
    ∃c,metadata.Executes g (initial (circuitBits n w))
      (SpectralDeltaDriver.frame (SourceFrontend.rawStore w 0 (List.replicate n true)) [] []) c ∧
      c ≤ CircuitMetadata.time.eval (circuitBits n w).length := by
  obtain ⟨c,hc,hb⟩:=ConstraintZero.metadata_executes g w
  have hl:=SpectralDeltaDriver.lift_executes _ g _ _ [] [] c hc
  rw [SpectralDeltaDriver.frame_initial] at hl
  exact ⟨c,hl,hb⟩
lemma core_executes (g : BitString→ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n)) :
    ∃c,core.Executes g (initial (circuitBits n w))
      (SpectralDeltaDriver.finalState w (SpectralDeltaDriver.result w)) c ∧
      c ≤ coreTime.eval (circuitBits n w).length := by
  obtain ⟨a,ha,hab⟩:=metadata_executes g w
  obtain ⟨am,hm,hmb⟩:=ConstraintZero.metadata_executes g w
  have hinit:∀i : Fin 64,(Function.update (fun _ : Fin 64=>([]:BitString)) 0 (circuitBits n w) i).length ≤ (circuitBits n w).length := by
    intro i;simp only [Function.update_apply];split_ifs <;> simp
  have hraw:=hm.stack_bound hinit
  have hbound:∀i,(SourceFrontend.rawStore w 0 (List.replicate n true) i).length ≤ (circuitBits n w).length+CircuitMetadata.time.eval (circuitBits n w).length := by
    intro i
    exact (hraw i).trans (Nat.add_le_add_left hmb _)
  obtain ⟨b,hb,hbb⟩:=SpectralDeltaDriver.program_executes g hg w (List.replicate n true)
    ((circuitBits n w).length+CircuitMetadata.time.eval (circuitBits n w).length) hbound
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [coreTime,eval_add,eval_comp,eval_X,eval_ofNat]
  omega

theorem program_executes (g : BitString→ℕ) (hg : DeltaOracle g) {n : ℕ} (w : List (ConstraintGate n)) :
    ∃c,program.Executes g (initial (circuitBits n w))
      (initial (RationalOracleEncoding.bits (constraintCircuitMatrix w (zeroBits n) (zeroBits n)))) c ∧
      c ≤ time.eval (circuitBits n w).length := by
  obtain ⟨a,ha,hab⟩:=core_executes g hg w
  have h11:SpectralDeltaDriver.finalState w (SpectralDeltaDriver.result w) 11=signedBits (SpectralDeltaDriver.result w).1 := by
    change SpectralDeltaDriver.finalState w (SpectralDeltaDriver.result w) (SpectralDeltaDriver.lowPort 11)=_
    rw [SpectralDeltaDriver.finalState_low];rfl
  have h12:SpectralDeltaDriver.finalState w (SpectralDeltaDriver.result w) 12=signedBits (SpectralDeltaDriver.result w).2 := by
    change SpectralDeltaDriver.finalState w (SpectralDeltaDriver.result w) (SpectralDeltaDriver.lowPort 12)=_
    rw [SpectralDeltaDriver.finalState_low];rfl
  have h24:SpectralDeltaDriver.finalState w (SpectralDeltaDriver.result w) 24=[] := by
    change SpectralDeltaDriver.finalState w (SpectralDeltaDriver.result w) (SpectralDeltaDriver.lowPort 24)=_
    rw [SpectralDeltaDriver.finalState_low];rfl
  obtain ⟨b,hb,hbb⟩:=finish_executes g _ (SpectralDeltaDriver.result w) ((circuitBits n w).length+a)
    h11 h12 h24 (ha.stack_bound (initial_bound _))
  rw [SpectralDeltaDriver.result_value] at hb
  have hm:=polynomial_nat_eval_mono timeFinish (Nat.add_le_add_left hab (circuitBits n w).length)
  dsimp only at hm
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  simp only [time,eval_add,eval_comp,eval_X,eval_ofNat]
  omega
end HiddenCircuits.Circuit.Runtime.SpectralConstraint
