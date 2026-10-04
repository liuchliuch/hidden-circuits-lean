import HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitterModel

namespace HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
open Complexity OracleBlock Polynomial

lemma chunk_length (a : GateTag) (p : ℕ) : (GateEmitter.chunk a p).length=2*p+20 := by
  simp [GateEmitter.chunk,GateEmitter.atomPrefix_length];omega
lemma gateOutput_length {n : ℕ} (a : ConstraintGate n) (r s : ℕ) :
    (gateOutput a r s).length ≤ (2*(r+s)+1)*(2*n+20) := by
  have hp : gatePosition a ≤ n := by have h:=gatePosition_bound a;omega
  cases a with
  | one p a=>
    rw [gateOutput_one,chunk_length]
    simp only [gatePosition] at hp
    nlinarith [Nat.zero_le ((r+s)*(2*n+20))]
  | forbid p=>
    rw [gateOutput_forbid,List.length_flatten,List.map_replicate,List.sum_replicate,chunk_length]
    simp only [nsmul_eq_mul]
    simp only [gatePosition] at hp
    nlinarith [Nat.mul_le_mul_left (2*r) (show 2*p.before+20 ≤ 2*n+20 by omega),Nat.zero_le (s*(2*n+20))]
  | controlledSign p=>
    rw [gateOutput_sign,List.length_flatten,List.map_replicate,List.sum_replicate,chunk_length]
    simp only [nsmul_eq_mul]
    simp only [gatePosition] at hp
    nlinarith [Nat.mul_le_mul_left (2*s) (show 2*p.before+20 ≤ 2*n+20 by omega),Nat.zero_le (r*(2*n+20))]
lemma output_length {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    (output w r s).length ≤ w.length*((2*(r+s)+1)*(2*n+20)) := by
  induction w with
  | nil=>simp [output_nil]
  | cons a w ih=>
    rw [output_cons,List.length_append,List.length_cons]
    have h:=gateOutput_length a r s
    nlinarith
lemma circuit_size_bounds {n : ℕ} (w : List (ConstraintGate n)) :
    n ≤ (circuitBits n w).length ∧ w.length ≤ (circuitBits n w).length := by
  have h:=list_length_le_encodeBitList_length (w.map gateBits)
  simp only [List.length_map] at h
  simp only [circuitBits,pairBits_length,List.length_replicate]
  omega
lemma query_length {n : ℕ} (w : List (ConstraintGate n)) (r s : ℕ) :
    (query w r s).encode.length ≤ 6*n+3+w.length*((2*(r+s)+1)*(2*n+20)) := by
  rw [query_encode]
  simp only [pairBits_length,List.length_replicate]
  have h:=output_length w r s;omega
end HiddenCircuits.Circuit.Runtime.SpectralDeltaEmitter
