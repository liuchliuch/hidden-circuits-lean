import HiddenCircuits.GraphReduction.Runtime.UnitRepresentationEncoding
import HiddenCircuits.GraphReduction.QueryRepresentations

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.BinaryArithmetic

def unitLeftInteger {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ)
    (i : Fin (unitGraphInput (fun r => ps.get r) S T s).1) : ℤ :=
  unitQueryLeftInteger ps ((unitEnumeration S T s).labels.get i)
def unitRepresentationBits {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) : BitString :=
  encodeBitList (signedBits (UnitInterval.commonLength (2*p) ps.length)::
    (unitEnumeration S T s).labels.map (fun v => signedBits (unitQueryLeftInteger ps v)))

 theorem unitRepresentationBits_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    UnitRepresentation.bits (2*p) ps.length (unitRecords (fun r => ps.get r) S T s)=unitRepresentationBits ps S T s := by
  unfold UnitRepresentation.bits UnitRepresentation.words unitRepresentationBits
  congr 2
  unfold unitRecords
  rw [List.map_map]
  apply List.map_congr_left
  intro v hv
  exact congrArg signedBits (unitCoordinate_correct ps S T s v)

 def decodeSignedInteger : BitString → ℤ
  | [] => 0
  | sign::magnitude => signedNat sign (value magnitude)
@[simp] theorem decodeSignedInteger_signedBits (z : ℤ) : decodeSignedInteger (signedBits z)=z := by
  simp [decodeSignedInteger,signedBits,value_encodeNat]

def decodeIntegerList (bs : BitString) : Option (List ℤ) := (decodeBitList bs).map (List.map decodeSignedInteger)

 theorem decode_unitRepresentationBits {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    decodeIntegerList (unitRepresentationBits ps S T s)=some
      (UnitInterval.commonLength (2*p) ps.length::(unitEnumeration S T s).labels.map (unitQueryLeftInteger ps)) := by
  simp [decodeIntegerList,unitRepresentationBits,List.map_map,Function.comp_def]

 theorem unitRepresentationLeft_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ)
    (i : Fin (unitGraphInput (fun r => ps.get r) S T s).1) :
    (unitMatrixRepresentation ps S T s).left i=(unitLeftInteger ps S T s i:ℚ)/(UnitInterval.commonLength (2*p) ps.length:ℚ) := by
  change (unitIntervalQueryRepresentation ps S T s).left ((unitEnumeration S T s).labels.get i)/
    (unitIntervalQueryRepresentation ps S T s).length=_
  rw [unitIntervalQuery_left_integer]
  rfl

 theorem unitRepresentation_adjacency {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ)
    (i j : Fin (unitGraphInput (fun r => ps.get r) S T s).1) :
    (unitGraphInput (fun r => ps.get r) S T s).2.graph.Adj i j ↔ i≠j ∧
      (Set.Icc ((unitLeftInteger ps S T s i:ℚ)/(UnitInterval.commonLength (2*p) ps.length:ℚ))
        ((unitLeftInteger ps S T s i:ℚ)/(UnitInterval.commonLength (2*p) ps.length:ℚ)+1) ∩
       Set.Icc ((unitLeftInteger ps S T s j:ℚ)/(UnitInterval.commonLength (2*p) ps.length:ℚ))
        ((unitLeftInteger ps S T s j:ℚ)/(UnitInterval.commonLength (2*p) ps.length:ℚ)+1)).Nonempty := by
  simpa only [unitRepresentationLeft_eq,unitMatrixRepresentation_length] using (unitMatrixRepresentation ps S T s).adjacency i j

end HiddenCircuits.GraphReduction.Runtime
