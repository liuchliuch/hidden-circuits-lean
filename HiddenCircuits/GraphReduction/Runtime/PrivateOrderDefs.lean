import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptor
import HiddenCircuits.GraphReduction.PrivateProbeQueries

/-! Fresh reconstruction: local record comparisons for the two actual private
endpoint orders. Equal-layer original comparisons use their literal cut tags. -/
namespace HiddenCircuits.GraphReduction.Runtime.PrivateOrder

def lowerLayer (x : VertexRecord) : ℕ := x.layer+(if x.side then 1 else 0)
def upperLocalLT (x y : VertexRecord) : Bool :=
  if x.probe then
    if x.side then y.probe && y.side && decide (x.track<y.track)
    else if y.probe && !y.side then decide (x.track<y.track) else true
  else if y.probe then y.side
  else if x.side==y.side then decide (y.track<x.track)
  else if x.side then cutBit x.cut.leftRise x.cut.leftDrop x.cut.index y.track x.track
  else !cutBit y.cut.leftRise y.cut.leftDrop y.cut.index x.track y.track

def lowerLocalLT (x y : VertexRecord) : Bool :=
  if x.probe then
    if x.side then if y.probe && y.side then decide (y.track<x.track) else true
    else y.probe && !y.side && decide (y.track<x.track)
  else if y.probe then !y.side
  else if x.side==y.side then decide (x.track<y.track)
  else if x.side then !cutBit x.cut.rightRise x.cut.rightDrop x.cut.index y.track x.track
  else cutBit y.cut.rightRise y.cut.rightDrop y.cut.index x.track y.track

def upperRecordLT (x y : VertexRecord) : Bool :=
  decide (x.layer<y.layer) || (decide (x.layer=y.layer) && upperLocalLT x y)
def lowerRecordLT (x y : VertexRecord) : Bool :=
  decide (lowerLayer x<lowerLayer y) || (decide (lowerLayer x=lowerLayer y) && lowerLocalLT x y)

def rawRecord {p h s : ℕ} (pairs : Fin h → CutPair p) : PrivateProbe.Vertex (2*p) h s → VertexRecord
  | .inl (.inl x) => ⟨false,false,x.1.val,x.2.val,backgroundCode⟩
  | .inl (.inr x) => ⟨true,false,x.1.val,x.2.val,cutCode (pairs x.1)⟩
  | .inr (.inl j,q) => ⟨false,true,j.val,q.val,backgroundCode⟩
  | .inr (.inr r,q) => ⟨true,true,r.val,q.val,backgroundCode⟩

lemma rawRecord_retained {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (v : PrivateQueryVertex p h s S T) :
    rawRecord pairs (PrivateProbe.retainedEmbedding S T s v)=privateVertexRecord pairs v := by
  rcases v with (x|x)|(⟨j|r,q⟩) <;> rfl
lemma upperLayer_eq {p h s : ℕ} (pairs : Fin h → CutPair p) (v : PrivateProbe.Vertex (2*p) h s) :
    (rawRecord pairs v).layer=(PrivateProbe.topBlock v).val := by
  rcases v with (x|x)|(⟨j|r,q⟩) <;> rfl
lemma lowerLayer_eq {p h s : ℕ} (pairs : Fin h → CutPair p) (v : PrivateProbe.Vertex (2*p) h s) :
    lowerLayer (rawRecord pairs v)=(PrivateProbe.bottomBlock v).val := by
  rcases v with (x|x)|(⟨j|r,q⟩) <;> simp [lowerLayer,rawRecord,PrivateProbe.bottomBlock]
end HiddenCircuits.GraphReduction.Runtime.PrivateOrder
