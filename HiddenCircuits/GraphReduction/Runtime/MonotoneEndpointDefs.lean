import HiddenCircuits.GraphReduction.Runtime.MonotoneDescriptor
import HiddenCircuits.GraphReduction.MonotoneEndpointEncoding

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneOrder

def lowerLayer (x : VertexRecord) : ℕ := x.layer+(if x.side || x.probe then 1 else 0)
def upperLocalLT (x y : VertexRecord) : Bool :=
  if x.probe then y.probe && (if x.side==y.side then decide (x.track<y.track) else x.side)
  else if y.probe then true
  else if x.side==y.side then decide (y.track<x.track)
  else if x.side then cutBit x.cut.leftRise x.cut.leftDrop x.cut.index y.track x.track
  else !cutBit y.cut.leftRise y.cut.leftDrop y.cut.index x.track y.track

def lowerLocalLT (x y : VertexRecord) : Bool :=
  if x.probe then
    if x.side then y.probe && y.side && decide (x.track<y.track)
    else if y.probe && !y.side then decide (x.track<y.track) else true
  else if y.probe then y.side
  else if x.side==y.side then decide (y.track<x.track)
  else if x.side then cutBit x.cut.rightRise x.cut.rightDrop x.cut.index y.track x.track
  else !cutBit y.cut.rightRise y.cut.rightDrop y.cut.index x.track y.track

def upperRecordLT (x y : VertexRecord) : Bool :=
  decide (x.layer<y.layer) || (decide (x.layer=y.layer) && upperLocalLT x y)
def lowerRecordLT (x y : VertexRecord) : Bool :=
  decide (lowerLayer x<lowerLayer y) || (decide (lowerLayer x=lowerLayer y) && lowerLocalLT x y)
end HiddenCircuits.GraphReduction.Runtime.MonotoneOrder

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity

def leftRank (records : List VertexRecord) (x : VertexRecord) : ℕ :=
  (records.filter (fun y=>!y.side && MonotoneOrder.upperRecordLT y x)).length
def upperCount (records : List VertexRecord) (x : VertexRecord) : ℕ :=
  (records.filter (fun y=>y.side && MonotoneOrder.upperRecordLT y x)).length
def lowerCount (records : List VertexRecord) (x : VertexRecord) : ℕ :=
  (records.filter (fun y=>y.side && MonotoneOrder.lowerRecordLT y x)).length
def orderedLeft (records : List VertexRecord) : List VertexRecord :=
  (List.range records.length).flatMap (fun k=>records.filter (fun x=>!x.side && decide (leftRank records x=k)))
def lowValue (records : List VertexRecord) (x : VertexRecord) : ℕ := min (upperCount records x) (lowerCount records x)
def highValue (records : List VertexRecord) (x : VertexRecord) : ℕ := max (upperCount records x) (lowerCount records x)
def bits (records : List VertexRecord) : BitString := encodeBitList
  [List.replicate (orderedLeft records).length true,
    encodeBitList ((orderedLeft records).map (fun x=>List.replicate (lowValue records x) true)),
    encodeBitList ((orderedLeft records).map (fun x=>List.replicate (highValue records x) true))]
noncomputable def leftCard (p h s : ℕ) (S T : State (2*p) p) : ℕ :=
  Fintype.card (ProbePart (RetainedEven p h S T) (Fin h) s)
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
