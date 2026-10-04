import HiddenCircuits.Circuit.Runtime.SourceReductionFrameCore
import HiddenCircuits.Circuit.Runtime.SourceOracleRuntime

/-! Exact boundary between the physically initialized
frontend, the three actual interpolation loops, and signed final division. -/
namespace HiddenCircuits.Circuit.Runtime.SourceReduction
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceFrontend

lemma state_eq_frame (k : ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (acc : ℤ×ℤ) :
    SourceOuter.state (k:=k) w a 0 acc=
      frame k (SourceSample.store (SourceSample.canonical w a 0 0 0) {accumulator:=acc})
        (List.replicate (Fintype.card (SpectralIndex (forbidOccurrences w))-1) true)
        (List.replicate (Fintype.card (SpectralIndex (signOccurrences w))-1) true) := rfl

theorem front_executes (k : ℕ) (g : BitString→ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ)
    (wire : BitString) (B : ℕ) (hB : ∀i,(rawStore w a wire i).length≤B) :
    ∃c,(front k).Executes g (frame k (rawStore w a wire) [] [])
      (SourceOuter.state (k:=k) w a 0 (0,1)) c ∧ c≤frontTime.eval B := by
  rw [state_eq_frame]
  exact front_frame_executes k g w a wire B hB

lemma final_port_eq (k : ℕ) (i : Fin 64) : SourceFinalization.port k i=lowPort k i := Fin.ext rfl
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
lemma final_projection (k : ℕ) {n : ℕ} (w : List (ConstraintGate n)) (a : ℕ) (acc : ℤ×ℤ) :
    SourceOuter.state (k:=k) w a 0 acc∘SourceFinalization.divisionEmbedding k=
      binaryStore (signedBits acc.1) (signedBits acc.2) := by
  rw [state_eq_frame]
  funext i
  simp only [Function.comp_apply]
  have hp : SourceFinalization.divisionEmbedding k i=
      lowPort k ((![11,12,24,25,26,27,28,29,30] : Fin 9→Fin 64) i) := Fin.ext rfl
  rw [hp,frame_low]
  fin_cases i <;> rfl

end HiddenCircuits.Circuit.Runtime.SourceReduction
