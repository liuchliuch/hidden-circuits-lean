import HiddenCircuits.GraphReduction.Runtime.MonotoneDescriptor
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorAtom
open Complexity Complexity.BinaryArithmetic

def tagBits (v : VertexRecord) : BitString :=
  [v.side,v.probe,v.cut.leftRise,v.cut.leftDrop,v.cut.rightRise,v.cut.rightDrop]

theorem payload_append (xs ys : BitString) : wordPayload (xs++ys)=wordPayload xs++wordPayload ys := by
  simp [wordPayload]
theorem payload_unary (n : ℕ) : wordPayload (List.replicate n true)=List.replicate (2*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,true]++wordPayload (List.replicate n true)=_
    rw [ih]
    simp [show 2*(n+1)=2*n+2 by omega,List.replicate_succ]

theorem payload_pair_unary (n : ℕ) (tail : BitString) :
    wordPayload (pairBits (List.replicate n true) tail)=
      List.replicate (4*n) true++[true,false]++wordPayload tail := by
  rw [pairBits_eq_payload,payload_append,payload_unary,payload_unary]
  simp [wordPayload,show 2*(2*n)=4*n by omega,List.append_assoc]

theorem vertex_chunk (v : VertexRecord) : wordChunk (encodeVertex v)=
    [true]++wordPayload (tagBits v)++List.replicate (4*v.layer) true++[true,false]++
      List.replicate (4*v.track) true++[true,false]++List.replicate (2*v.cut.index) true++[false] := by
  rw [wordChunk_eq]
  change true::(wordPayload (tagBits v++pairBits (List.replicate v.layer true)
    (pairBits (List.replicate v.track true) (List.replicate v.cut.index true)))++[false])=_
  rw [payload_append,payload_pair_unary,payload_pair_unary,payload_unary]
  simp [List.append_assoc]
end HiddenCircuits.GraphReduction.Runtime.DescriptorAtom
