import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateFormula
import HiddenCircuits.GraphReduction.Runtime.RecordParser
import HiddenCircuits.GraphReduction.Runtime.BooleanGates
import HiddenCircuits.GraphReduction.Runtime.UnarySuccessor

/-! Fixed comparisons and Boolean gates for a signed descriptor
contribution. The width comparison handles the last-track midpoint exactly. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCorrection
open Complexity Complexity.OracleBlock

def shifted (second : Bool) (width : ℕ) (x : VertexRecord) : Bool :=
  x.side && !x.probe &&
    ((decide (x.track=x.cut.index) && (x.cut.leftRise || x.cut.rightRise)) ||
      (!(decide (x.track=x.cut.index) && (x.cut.leftRise || x.cut.rightRise || x.cut.leftDrop || x.cut.rightDrop)) &&
        second && decide (x.track+1<width)))
lemma correctionTrack_shifted (second : Bool) (width : ℕ) (x : VertexRecord) :
    correctionTrack second width x=if shifted second width x then x.track+1 else x.track := by
  rcases x with ⟨side,probe,layer,track,⟨lr,ld,rr,rd,index⟩⟩
  cases side <;> cases probe <;> cases lr <;> cases ld <;> cases rr <;> cases rd <;>
    cases second <;> by_cases he : track=index <;> by_cases hb : track+1<width <;>
    simp [correctionTrack,shifted,UnitBaseline.mode,he,hb]

def active (x y : VertexRecord) : Bool :=
  y.side && !y.probe && decide (y.layer<x.layer) && decide (y.track=0)
def positive (second : Bool) (width : ℕ) (x y : VertexRecord) : Bool :=
  active x y && ((y.cut.leftRise && decide (correctionTrack second width x=y.cut.index+1)) ||
    (y.cut.rightDrop && decide (correctionTrack second width x=y.cut.index)))
def negativeRaw (second : Bool) (width : ℕ) (x y : VertexRecord) : Bool :=
  active x y && ((y.cut.rightRise && decide (correctionTrack second width x=y.cut.index+1)) ||
    (y.cut.leftDrop && decide (correctionTrack second width x=y.cut.index)))
def negative (second : Bool) (width : ℕ) (x y : VertexRecord) : Bool :=
  !(positive second width x y) && negativeRaw second width x y

def bits (second : Bool) (width : ℕ) (x y : VertexRecord) : Fin 14 → Bool :=
  ![decide (x.track=x.cut.index),decide (x.track+1<width),decide (y.layer<x.layer),decide (y.track=0),
    decide (x.track=y.cut.index),decide (x.track=y.cut.index+1),decide (x.track+1=y.cut.index),
    decide (x.track+1=y.cut.index+1),shifted second width x,
    decide (correctionTrack second width x=y.cut.index),decide (correctionTrack second width x=y.cut.index+1),
    positive second width x y,negativeRaw second width x y,negative second width x y]

lemma positive_eq (second : Bool) (width : ℕ) (x y : VertexRecord) :
    positive second width x y=decide (unitCorrectionValue second width x y=1) := by
  have h (a b c : Bool) : (a && b)=decide ((if a then if b then (1:ℤ) else if c then -1 else 0 else 0)=1) := by
    cases a <;> cases b <;> cases c <;> rfl
  exact h (active x y)
    ((y.cut.leftRise && decide (correctionTrack second width x=y.cut.index+1)) ||
      (y.cut.rightDrop && decide (correctionTrack second width x=y.cut.index)))
    ((y.cut.rightRise && decide (correctionTrack second width x=y.cut.index+1)) ||
      (y.cut.leftDrop && decide (correctionTrack second width x=y.cut.index)))
lemma negative_eq (second : Bool) (width : ℕ) (x y : VertexRecord) :
    negative second width x y=decide (unitCorrectionValue second width x y=-1) := by
  have h (a b c : Bool) : (!(a && b) && (a && c))=decide ((if a then if b then (1:ℤ) else if c then -1 else 0 else 0)=-1) := by
    cases a <;> cases b <;> cases c <;> rfl
  exact h (active x y)
    ((y.cut.leftRise && decide (correctionTrack second width x=y.cut.index+1)) ||
      (y.cut.rightDrop && decide (correctionTrack second width x=y.cut.index)))
    ((y.cut.rightRise && decide (correctionTrack second width x=y.cut.index+1)) ||
      (y.cut.leftDrop && decide (correctionTrack second width x=y.cut.index)))

def size (width : ℕ) (x y : VertexRecord) : ℕ :=
  width+x.layer+x.track+x.cut.index+y.layer+y.track+y.cut.index+2

def state (second : Bool) (width : ℕ) (x y : VertexRecord) (prepared : ℕ) (j : ℕ)
    (out : BitString := []) : Store 48 := fun i=>
  if h:i.val<9 then recordFields x ⟨i.val,h⟩ else
  if h:i.val<18 then recordFields y ⟨i.val-9,by omega⟩ else
  if i.val=18 then List.replicate width true else if i.val=19 then out else
  if i.val=20 then if 0<prepared then List.replicate (x.track+1) true else [] else
  if i.val=21 then if 1<prepared then List.replicate (y.cut.index+1) true else [] else
  if h : 22 ≤ i.val ∧ i.val < 36 then if i.val<22+j then [bits second width x y ⟨i.val-22,by omega⟩] else [] else []

 def successorMap (right : Bool) : Fin 3 ↪ Fin 49 where
  toFun i := if right then ![17,21,44] i else ![7,20,44] i
  inj' := by cases right <;> decide +kernel
 def compareMap (j : Fin 8) : Fin 6 ↪ Fin 49 where
  toFun i := ![(![7,20,15,16,7,7,20,20] j),(![8,18,6,48,17,21,17,21] j),
    (⟨22+j.val,by omega⟩ : Fin 49),45,46,47] i
  inj' := by fin_cases j <;> decide +kernel
 noncomputable def compare (j : Fin 8) : OracleBlock 48 :=
  if j=1 ∨ j=2 then readOnlyLTOn (compareMap j) else Complexity.GraphVerifier.Runtime.readLengthOn (compareMap j)

end HiddenCircuits.GraphReduction.Runtime.UnitCorrection
