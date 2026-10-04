import HiddenCircuits.Circuit.Runtime.SourceCircuitCore

/-! Bounds on the literal source-circuit bytes and actual unary normalization
clock, used to charge the final reversals and cleanup. -/
namespace HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
open HiddenCircuits.Complexity Polynomial

lemma gateStream_length {n : ℕ} (gs : List (ConstraintGate n)) :
    (SourceScan.gateStream gs).length≤gs.length*(2*n+20) := by
  induction gs with
  | nil => simp [SourceScan.gateStream,encodeBitList]
  | cons g gs ih =>
    have hp := gatePosition_bound g
    have hb : gatePosition g≤n := by omega
    simp only [SourceScan.gateStream,List.map_cons,encodeBitList,List.length_cons,pairBits_length,
      gateBits_length,List.length_cons] at *
    nlinarith

noncomputable def circuitSize : Polynomial ℕ := 2*X+1+(2*X+X^2*(18*X+1))*(2*X+20)

lemma circuitSize_bound {n : ℕ} (G : MatrixGraph n) :
    (circuitBits n (restoringIndependentProgram G).gates).length≤circuitSize.eval n := by
  rw [circuitBits_header,List.length_append]
  have hs := gateStream_length (restoringIndependentProgram G).gates
  have hg := restoringIndependentProgram_length G
  have hm := Nat.mul_le_mul_right (2*n+20) hg
  simp only [headerBits,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  simp only [circuitSize,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat,eval_one]
  omega

lemma normalization_bound {n : ℕ} (G : MatrixGraph n) :
    2*restoringSwapPairs (sourceEdges G)≤2*n^3 := by
  have hs := restoringSwapPairs_bound (sourceEdges G)
  rw [sourceEdges_length] at hs
  have he := orderedEdges_length_bound G
  have hm := Nat.mul_le_mul he (show n-1≤n by omega)
  nlinarith

end HiddenCircuits.Circuit.Runtime.SourceCircuitEmitter
