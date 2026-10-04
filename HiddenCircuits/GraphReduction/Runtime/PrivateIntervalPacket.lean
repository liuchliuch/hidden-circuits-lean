import HiddenCircuits.GraphReduction.Runtime.PrivateIntervalCorrect
import HiddenCircuits.GraphReduction.Runtime.PrivateSuppliedQuery

/-! A self-contained supplied packet contains the graph, both permutation
orders, and both integer interval endpoint vectors. -/
namespace HiddenCircuits.GraphReduction
open Complexity
set_option maxHeartbeats 1000000

/-- Nested triple framing preserves the existing graph-and-permutation packet. -/
def suppliedIntervalPermutationBits (G : GraphInput) (D : PermutationDiagram (Fin G.1))
    (I : Interval.NatRepresentation G.2.graph) : BitString :=
  encodeBitList [
    encodeBitList [G.encode,
      encodeBitList (List.ofFn (fun i => List.replicate (D.upper i) true)),
      encodeBitList (List.ofFn (fun i => List.replicate (D.lower i) true))],
    encodeBitList (List.ofFn (fun i => List.replicate (I.left i) true)),
    encodeBitList (List.ofFn (fun i => List.replicate (I.right i) true))]

/-- Every supplied interval and permutation diagram must describe the explicit graph. -/
def SuppliedIntervalPermutationOracle (g : BitString → ℕ) : Prop :=
  ∀ (G : GraphInput) (D : PermutationDiagram (Fin G.1))
    (I : Interval.NatRepresentation G.2.graph), D.graph=G.2.graph →
      g (suppliedIntervalPermutationBits G D I)=perfectMatchingCount G.2.graph

namespace Runtime.PrivateBothQuery

def bits {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : BitString :=
  encodeBitList [PrivateSuppliedQuery.bits pairs S T s,
    PrivateInterval.bits true (privateRecords pairs S T s),
    PrivateInterval.bits false (privateRecords pairs S T s)]

lemma bits_correct {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    bits pairs S T s=suppliedIntervalPermutationBits (privateGraphInput pairs S T s)
      (privateMatrixDiagram pairs S T s) (privateMatrixIntervalRepresentation pairs S T s) := by
  unfold bits
  rw [PrivateInterval.bits_correct,PrivateInterval.bits_correct]
  rfl

lemma intervalBits_length (left : Bool) (records : List VertexRecord) :
    (PrivateInterval.bits left records).length ≤ 2*records.length^2+2*records.length := by
  simpa only [PrivateInterval.bits,pow_two,Nat.mul_assoc] using
    RankEmitter.bits_length_bound records.length (PrivateInterval.endpointEdge left records)

lemma bits_length {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (bits pairs S T s).length ≤ 28*(privateGraphInput pairs S T s).1^2+
      32*(privateGraphInput pairs S T s).1+22 := by
  let N := (privateGraphInput pairs S T s).1
  let R := privateRecords pairs S T s
  have hR : R.length=N := privateRecords_length pairs S T s
  have hL := intervalBits_length true R
  have hU := intervalBits_length false R
  rw [hR] at hL hU
  have hP : (PrivateSuppliedQuery.bits pairs S T s).length ≤ 10*N^2+12*N+8 := by
    have hu := PrivateSuppliedQuery.bits_length_rank false R
    have hv := PrivateSuppliedQuery.bits_length_rank true R
    rw [hR] at hu hv
    have hG := GraphInput.encode_length (privateGraphInput pairs S T s)
    have hp : PrivateSuppliedQuery.bits pairs S T s=encodeBitList
        [(privateGraphInput pairs S T s).encode,PrivateRankEmitter.bits false R,PrivateRankEmitter.bits true R] := by
      dsimp only [R,PrivateSuppliedQuery.bits]
      rw [PrivateRankEmitter.upper_bits_correct,PrivateRankEmitter.lower_bits_correct]
    rw [hp]
    simp only [encodeBitList,List.length_cons,pairBits_length,List.length_nil]
    dsimp only [N] at hu hv ⊢
    nlinarith
  simp only [bits,encodeBitList,List.length_cons,pairBits_length,List.length_nil]
  dsimp only [N] at hL hU hP ⊢
  dsimp only [R] at hL hU
  nlinarith

end Runtime.PrivateBothQuery
end HiddenCircuits.GraphReduction
