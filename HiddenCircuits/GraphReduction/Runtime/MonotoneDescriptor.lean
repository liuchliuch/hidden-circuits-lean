import HiddenCircuits.GraphReduction.QueryEncoding
import HiddenCircuits.Complexity.BitList

/-! Structural vertex descriptors for the exact Section 9 query enumeration.
Descriptors contain cut tags and unary coordinates, never adjacency bits. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity

 structure CutCode where
  leftRise : Bool
  leftDrop : Bool
  rightRise : Bool
  rightDrop : Bool
  index : ℕ
  deriving DecidableEq

 def cutCode {p : ℕ} : CutPair p → CutCode
  | .background => ⟨false,false,false,false,0⟩
  | .leftRise i => ⟨true,false,false,false,i.val⟩
  | .leftDrop i => ⟨false,true,false,false,i.val⟩
  | .rightRise i => ⟨false,false,true,false,i.val⟩
  | .rightDrop i => ⟨false,false,false,true,i.val⟩

 def cutBit (rise drop : Bool) (index x y : ℕ) : Bool :=
  (decide (x≤y) || (rise && decide (x=index+1) && decide (y=index))) &&
    !(drop && decide (x=index) && decide (y=index))

 theorem cutBit_first {p : ℕ} (P : CutPair p) (x y : Fin (2*p)) :
    cutBit (cutCode P).leftRise (cutCode P).leftDrop (cutCode P).index x.val y.val =
      decide (P.first x y=1) := by
  cases P <;> simp only [cutCode,CutPair.first,cutBit]
  all_goals simp [addedCut,deletedCut,upper,Bool.or_comm,Bool.and_comm]
  all_goals split_ifs <;> simp_all <;> tauto

 theorem cutBit_second {p : ℕ} (P : CutPair p) (x y : Fin (2*p)) :
    cutBit (cutCode P).rightRise (cutCode P).rightDrop (cutCode P).index x.val y.val =
      decide (P.second y x=1) := by
  cases P <;> simp only [cutCode,CutPair.second,cutBit,Matrix.transpose_apply]
  all_goals simp [addedCut,deletedCut,upper,Bool.or_comm,Bool.and_comm]
  all_goals split_ifs <;> simp_all <;> tauto

 structure VertexRecord where
  side : Bool
  probe : Bool
  layer : ℕ
  track : ℕ
  cut : CutCode
  deriving DecidableEq

 def backgroundCode : CutCode := ⟨false,false,false,false,0⟩

 abbrev QueryVertex (p h s : ℕ) (S T : State (2*p) p) :=
  ProbePart (RetainedEven p h S T) (Fin h) s ⊕ ProbePart (OddVertex (2*p) h) (Fin h) s

 def vertexRecord {p h s : ℕ} (pairs : Fin h → CutPair p) {S T : State (2*p) p} :
    QueryVertex p h s S T → VertexRecord
  | .inl (.inl x) => ⟨false,false,x.val.1.val,x.val.2.val,backgroundCode⟩
  | .inl (.inr x) => ⟨false,true,x.1.val,x.2.val,backgroundCode⟩
  | .inr (.inl y) => ⟨true,false,y.1.val,y.2.val,cutCode (pairs y.1)⟩
  | .inr (.inr y) => ⟨true,true,y.1.val,y.2.val,backgroundCode⟩

/-- The local rule is orientation-aware, with the second original cut complemented. -/
 def directedRecordAdj (x y : VertexRecord) : Bool :=
  !x.side && y.side &&
    (if x.probe then decide (x.layer=y.layer)
    else if y.probe then decide (x.layer=y.layer+1)
    else (decide (x.layer=y.layer) && cutBit y.cut.leftRise y.cut.leftDrop y.cut.index x.track y.track) ||
      (decide (x.layer=y.layer+1) && !cutBit y.cut.rightRise y.cut.rightDrop y.cut.index x.track y.track))
 def recordAdj (x y : VertexRecord) : Bool := if x.side then directedRecordAdj y x else directedRecordAdj x y

 theorem original_directed {p h : ℕ} (pairs : Fin h → CutPair p)
    (x : EvenVertex (2*p) h) (y : OddVertex (2*p) h) :
    directedRecordAdj ⟨false,false,x.1.val,x.2.val,backgroundCode⟩
      ⟨true,false,y.1.val,y.2.val,cutCode (pairs y.1)⟩ = decide (queryRelation pairs x y) := by
  simp only [directedRecordAdj,Bool.not_false,Bool.true_and,Bool.false_eq_true,ite_false]
  rw [cutBit_first,cutBit_second]
  simp [queryRelation]

 theorem recordAdj_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : QueryVertex p h s S T) :
    recordAdj (vertexRecord pairs x) (vertexRecord pairs y)=decide ((monotoneQueryGraph pairs S T s).Adj x y) := by
  rcases x with (x|x)|(x|x) <;> rcases y with (y|y)|(y|y)
  all_goals simp only [vertexRecord,recordAdj,directedRecordAdj,monotoneQueryGraph,probeGraph,cutGraph,
    SimpleGraph.fromRel_adj,probeRelation,retainedQueryRelation,retainedEvenAttachment,evenAttachment,oddAttachment]
  all_goals first
    | exact original_directed pairs _ _
    | simpa only [directedRecordAdj] using (original_directed pairs y.val x)
    | simp [Bool.and_assoc,Fin.ext_iff,eq_comm]

/-- Two kind bits, four one-hot cut tag bits, and three unary coordinates. -/
 def encodeVertex (v : VertexRecord) : BitString :=
  [v.side,v.probe,v.cut.leftRise,v.cut.leftDrop,v.cut.rightRise,v.cut.rightDrop] ++
    pairBits (List.replicate v.layer true)
      (pairBits (List.replicate v.track true) (List.replicate v.cut.index true))

 @[simp] theorem encodeVertex_length (v : VertexRecord) :
    (encodeVertex v).length=8+2*v.layer+2*v.track+v.cut.index := by
  simp [encodeVertex]; omega

 def monotoneRecords {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : List VertexRecord :=
  (monotoneEnumeration S T s).labels.map (vertexRecord pairs)
 def monotoneDescriptor {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : BitString :=
  encodeBitList ((monotoneRecords pairs S T s).map encodeVertex)

 theorem monotoneRecords_length {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (monotoneRecords pairs S T s).length=(monotoneGraphInput pairs S T s).1 := by
  simp [monotoneRecords,monotoneGraphInput,Enumeration.graphInput]

 theorem monotoneRecord_edge {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ)
    (i j : Fin (monotoneGraphInput pairs S T s).1) :
    recordAdj (vertexRecord pairs ((monotoneEnumeration S T s).labels.get i))
      (vertexRecord pairs ((monotoneEnumeration S T s).labels.get j)) =
      (monotoneGraphInput pairs S T s).2.edge i j := recordAdj_correct pairs S T _ _

 theorem cutCode_index_le {p : ℕ} (P : CutPair p) : (cutCode P).index≤2*p := by
  cases P <;> simp [cutCode] <;> omega

 theorem vertexRecord_bounds {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (v : QueryVertex p h s S T) :
    (vertexRecord pairs v).layer≤h ∧ (vertexRecord pairs v).track≤2*p+s ∧
      (vertexRecord pairs v).cut.index≤2*p := by
  rcases v with (v|v)|(v|v)
  · simp only [vertexRecord,backgroundCode]
    exact ⟨by omega,by omega,by omega⟩
  · simp only [vertexRecord,backgroundCode]
    exact ⟨by omega,by omega,by omega⟩
  · simp only [vertexRecord]
    exact ⟨by omega,by omega,cutCode_index_le _⟩
  · simp only [vertexRecord,backgroundCode]
    exact ⟨by omega,by omega,by omega⟩

 theorem encoded_record_bound {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (v : QueryVertex p h s S T) :
    (encodeVertex (vertexRecord pairs v)).length≤8+2*h+6*p+2*s := by
  have hv := vertexRecord_bounds pairs S T v
  rw [encodeVertex_length]
  omega

end HiddenCircuits.GraphReduction.Runtime
