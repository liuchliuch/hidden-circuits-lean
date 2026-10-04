import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateFormula
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! The literal signed denominator-and-left-endpoint payload. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
open Complexity Complexity.BinaryArithmetic

def words (width height : ℕ) (records : List VertexRecord) : List BitString :=
  signedBits (UnitInterval.commonLength width height)::
    records.map (fun x=>signedBits (unitCoordinate width height records x))
def bits (width height : ℕ) (records : List VertexRecord) : BitString :=
  encodeBitList (words width height records)

@[simp] theorem decode_bits (width height : ℕ) (records : List VertexRecord) :
    decodeBitList (bits width height records)=some (words width height records) :=
  by simp [bits]
end HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
