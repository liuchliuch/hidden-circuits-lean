import HiddenCircuits.GraphReduction.Runtime.MonotoneDescriptor

/-! Literal structural records for both clique-probe families. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity

abbrev UnitQueryVertex (p h s : ℕ) (S T : State (2*p) p) := UnitOriginalVertex p h S T ⊕ (Fin (h+1) × Fin s)
abbrev PrivateQueryVertex (p h s : ℕ) (S T : State (2*p) p) := PrivateProbe.RetainedOriginal p h S T ⊕ (PrivateProbe.Layer h × Fin s)

def unitVertexRecord {p h s : ℕ} (pairs : Fin h → CutPair p) {S T : State (2*p) p} : UnitQueryVertex p h s S T → VertexRecord
  | .inl (.inl x) => ⟨false,false,x.val.1.val,x.val.2.val,backgroundCode⟩
  | .inl (.inr y) => ⟨true,false,y.1.val,y.2.val,cutCode (pairs y.1)⟩
  | .inr x => ⟨false,true,x.1.val,x.2.val,backgroundCode⟩

def privateVertexRecord {p h s : ℕ} (pairs : Fin h → CutPair p) {S T : State (2*p) p} : PrivateQueryVertex p h s S T → VertexRecord
  | .inl (.inl x) => ⟨false,false,x.val.1.val,x.val.2.val,backgroundCode⟩
  | .inl (.inr y) => ⟨true,false,y.1.val,y.2.val,cutCode (pairs y.1)⟩
  | .inr (.inl j,q) => ⟨false,true,j.val,q.val,backgroundCode⟩
  | .inr (.inr r,q) => ⟨true,true,r.val,q.val,backgroundCode⟩

def unitRecords {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : List VertexRecord :=
  (unitEnumeration S T s).labels.map (unitVertexRecord pairs)
def privateRecords {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : List VertexRecord :=
  (privateEnumeration S T s).labels.map (privateVertexRecord pairs)
def unitDescriptor {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : BitString := encodeBitList ((unitRecords pairs S T s).map encodeVertex)
def privateDescriptor {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : BitString := encodeBitList ((privateRecords pairs S T s).map encodeVertex)

lemma unitRecords_length {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (unitRecords pairs S T s).length=(unitGraphInput pairs S T s).1 := by simp [unitRecords,unitGraphInput,Enumeration.graphInput]
lemma privateRecords_length {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (privateRecords pairs S T s).length=(privateGraphInput pairs S T s).1 := by simp [privateRecords,privateGraphInput,Enumeration.graphInput]

/-- False complements the first cut; true leaves both cuts unchanged. -/
def cliqueDirectedRecordAdj (mode : Bool) (x y : VertexRecord) : Bool :=
  !x.side && y.side && !x.probe && !y.probe &&
    ((decide (x.layer=y.layer) && (if mode then cutBit y.cut.leftRise y.cut.leftDrop y.cut.index x.track y.track
      else !(cutBit y.cut.leftRise y.cut.leftDrop y.cut.index x.track y.track))) ||
      (decide (x.layer=y.layer+1) && cutBit y.cut.rightRise y.cut.rightDrop y.cut.index x.track y.track))

def cliqueLocalAdj (mode : Bool) (x y : VertexRecord) : Bool :=
  decide (x.layer=y.layer) &&
    (if x.probe || y.probe then
      (if mode then decide (x.side=y.side) else true) && (if x.probe && y.probe then !decide (x.track=y.track) else true)
    else decide (x.side=y.side) && !decide (x.track=y.track))
def cliqueRecordAdj (mode : Bool) (x y : VertexRecord) : Bool :=
  cliqueDirectedRecordAdj mode x y || cliqueDirectedRecordAdj mode y x || cliqueLocalAdj mode x y

end HiddenCircuits.GraphReduction.Runtime
