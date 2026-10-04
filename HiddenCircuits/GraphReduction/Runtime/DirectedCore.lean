import HiddenCircuits.GraphReduction.Runtime.RecordPrefix
import HiddenCircuits.GraphReduction.Runtime.BooleanGates
import HiddenCircuits.GraphReduction.Runtime.UnaryCompare

/-! Register semantics for the actual directed structural adjacency predicate. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

def dirStore (x y : VertexRecord) (layerPlus indexPlus : BitString)
    (flags : Fin 11 → BitString) (output : BitString) : Store 40 :=
  fun i =>
    if i.val=0 then recordFields x 0 else
    if i.val=1 then recordFields x 1 else
    if i.val=2 then recordFields x 2 else
    if i.val=3 then recordFields x 3 else
    if i.val=4 then recordFields x 4 else
    if i.val=5 then recordFields x 5 else
    if i.val=6 then recordFields x 6 else
    if i.val=7 then recordFields x 7 else
    if i.val=8 then recordFields x 8 else
    if i.val=9 then recordFields y 0 else
    if i.val=10 then recordFields y 1 else
    if i.val=11 then recordFields y 2 else
    if i.val=12 then recordFields y 3 else
    if i.val=13 then recordFields y 4 else
    if i.val=14 then recordFields y 5 else
    if i.val=15 then recordFields y 6 else
    if i.val=16 then recordFields y 7 else
    if i.val=17 then recordFields y 8 else
    if i.val=18 then output else
    if i.val=19 then layerPlus else
    if i.val=20 then indexPlus else
    if i.val=21 then flags 0 else
    if i.val=22 then flags 1 else
    if i.val=23 then flags 2 else
    if i.val=24 then flags 3 else
    if i.val=25 then flags 4 else
    if i.val=26 then flags 5 else
    if i.val=27 then flags 6 else
    if i.val=28 then flags 7 else
    if i.val=29 then flags 8 else
    if i.val=30 then flags 9 else
    if i.val=31 then flags 10 else []

def dirBits (x y : VertexRecord) : Fin 11 → Bool :=
  ![decide (x.layer=y.layer),decide (x.layer=y.layer+1),decide (y.track<x.track),
    decide (x.track=y.cut.index),decide (x.track=y.cut.index+1),decide (y.track=y.cut.index),
    decide (x.track=y.cut.index+1) && decide (y.track=y.cut.index),
    decide (x.track=y.cut.index) && decide (y.track=y.cut.index),
    !decide (y.track<x.track),
    cutBit y.cut.leftRise y.cut.leftDrop y.cut.index x.track y.track,
    cutBit y.cut.rightRise y.cut.rightDrop y.cut.index x.track y.track]

def dirState (x y : VertexRecord) (count : ℕ) (output : BitString := []) : Store 40 :=
  dirStore x y (List.replicate (y.layer+1) true) (List.replicate (y.cut.index+1) true)
    (fun i => if i.val<count then [dirBits x y i] else []) output

def dirSize (x y : VertexRecord) : ℕ := (encodeVertex x).length+(encodeVertex y).length+1

def andGate : List Bool → Bool
  | a::b::_ => a && b
  | _ => false
def notGate : List Bool → Bool
  | a::_ => !a
  | _ => false
def orGate : List Bool → Bool
  | a::b::_ => a || b
  | _ => false
def cutGate : List Bool → Bool
  | [base,rise,drop,rising,dropping,_,_,_] => (base || (rise && rising)) && !(drop && dropping)
  | _ => false
def directedGate : List Bool → Bool
  | [leftSide,rightSide,leftProbe,rightProbe,sameLayer,nextLayer,first,second] =>
    !leftSide && rightSide && (if leftProbe then sameLayer else if rightProbe then nextLayer
      else (sameLayer && first) || (nextLayer && !second))
  | _ => false

lemma reverse_lt_neg (x y : ℕ) : (!decide (y<x))=decide (x≤y) := by
  by_cases h : y<x
  · have hn : ¬x≤y := by omega
    simp [h,hn]
  · have hn : x≤y := by omega
    simp [h,hn]

lemma recordAdj_or (x y : VertexRecord) :
    recordAdj x y = (directedRecordAdj x y || directedRecordAdj y x) := by
  cases hx:x.side <;> cases hy:y.side <;> simp [recordAdj,directedRecordAdj,hx,hy]

lemma recordFields_length (v : VertexRecord) (i : Fin 9) :
    (recordFields v i).length≤(encodeVertex v).length := by
  fin_cases i <;> simp [recordFields,encodeVertex_length] <;> omega

lemma dirSize_pos (x y : VertexRecord) : 0<dirSize x y := by unfold dirSize; omega

lemma dir_coordinates_bound (x y : VertexRecord) :
    x.layer≤dirSize x y ∧ x.track≤dirSize x y ∧ x.cut.index≤dirSize x y ∧
      y.layer+1≤dirSize x y ∧ y.track≤dirSize x y ∧ y.cut.index+1≤dirSize x y := by
  simp only [dirSize,encodeVertex_length]
  omega

lemma dirState_length (x y : VertexRecord) (count : ℕ) (out : BitString) (ho : out.length≤1)
    (i : Fin 41) : (dirState x y count out i).length≤dirSize x y := by
  have hc := dir_coordinates_bound x y
  have hp := dirSize_pos x y
  fin_cases i <;> simp [dirState,dirStore,recordFields] <;> (try split_ifs) <;> simp_all <;> omega

end HiddenCircuits.GraphReduction.Runtime
