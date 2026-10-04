import HiddenCircuits.Circuit.Runtime.DeltaAnswerBounds
import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterBounds

namespace HiddenCircuits.Circuit.Runtime.DeltaOracleRuntime
open Complexity OracleBlock BinaryArithmetic Polynomial

lemma input_bounds (C : DeltaInput) : C.wires ≤ C.encode.length ∧ C.gates.length ≤ C.encode.length := by
  have h:=SpectralDeltaEmitter.circuit_size_bounds (C.gates.map Complexity.DeltaGate.descriptor)
  simp only [List.length_map] at h
  have he : C.encode.length=4*C.wires+2+(circuitBits C.wires (C.gates.map Complexity.DeltaGate.descriptor)).length := by
    simp [DeltaInput.encode,DeltaInput.descriptor,ConstraintInput.encode,BoundaryTransport.inputBits]
    omega
  rw [he]
  omega
lemma answer_length (C : DeltaInput) : (RationalOracleEncoding.bits C.value).length ≤ 16*(C.encode.length+1)^2 := by
  have h:=DeltaValues.rational_bits_length C.gates C.source C.target
  obtain ⟨hn,hm⟩:=input_bounds C
  have hp:=Nat.mul_le_mul (show 2*C.wires+9 ≤ 2*C.encode.length+9 by omega) hm
  change (RationalOracleEncoding.bits C.value).length ≤ (2*C.wires+9)*C.gates.length+7 at h
  nlinarith
noncomputable def time : Polynomial ℕ := 1+X+16*(X+1)^2
lemma query_executes {k : ℕ} (port : Fin (k+1)) (g : BitString→ℕ) (hg : DeltaOracle g)
    (C : DeltaInput) (s : Store k) (hs : s port=C.encode) :
    (query port port).Executes g s (Function.update s port (RationalOracleEncoding.bits C.value))
      (1+C.encode.length+(RationalOracleEncoding.bits C.value).length) := by
  convert OracleBlock.query_executes g port port s using 1
  · simp only [OracleMachine.answerBits,hs,hg C,RationalOracleEncoding.encode_code]
  · simp only [OracleMachine.answerBits,hs,hg C,RationalOracleEncoding.encode_code]
lemma query_time (C : DeltaInput) :
    1+C.encode.length+(RationalOracleEncoding.bits C.value).length ≤ time.eval C.encode.length := by
  have h:=answer_length C
  simp only [time,eval_add,eval_one,eval_X,eval_mul,eval_ofNat,eval_pow]
  omega
end HiddenCircuits.Circuit.Runtime.DeltaOracleRuntime
