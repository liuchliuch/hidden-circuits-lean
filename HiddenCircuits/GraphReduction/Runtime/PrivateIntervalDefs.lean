import HiddenCircuits.GraphReduction.Runtime.PrivateOrderDefs
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackDefs
import HiddenCircuits.GraphReduction.PrivateIntervalRepresentation

/-! Structural comparisons for the two supplied private interval endpoint scans. -/
namespace HiddenCircuits.GraphReduction.Runtime.PrivateInterval

/-- Within each doubled layer, probes precede originals. Odd originals increase
in track number; even originals decrease. Probe copies increase in track. -/
def localLT (x y : VertexRecord) : Bool :=
  if x.side == y.side then
    if x.probe == y.probe then
      if x.probe || x.side then decide (x.track < y.track) else decide (y.track < x.track)
    else x.probe
  else !x.side

def recordLT (x y : VertexRecord) : Bool :=
  decide (x.layer < y.layer) || (decide (x.layer=y.layer) && localLT x y)

def endpointEdge (left : Bool) (records : List VertexRecord) (i j : ℕ) : Bool :=
  let x := records[j]?.getD defaultRecord
  let y := records[i]?.getD defaultRecord
  recordLT x y && (if left then !(cliqueRecordAdj true x y) else true)

end HiddenCircuits.GraphReduction.Runtime.PrivateInterval
