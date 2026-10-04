import HiddenCircuits.GraphReduction.Runtime.MonotoneDescriptor
import HiddenCircuits.GraphReduction.UnitIntervalProfileBounds
import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine

/-! Literal signed affine programs for the seven
Section 10 coordinate modes. No coordinate or execution certificate is an input. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.BinaryArithmetic RegisterMachine

namespace UnitBaseline
inductive Mode where
  | probe | even | ordinary | risePlus | riseMinus | dropPlus | dropMinus
  deriving DecidableEq

def mode (x : VertexRecord) : Mode :=
  if x.probe then .probe else if !x.side then .even else
    if x.track=x.cut.index then
      if x.cut.leftRise then .risePlus else if x.cut.rightRise then .riseMinus else
      if x.cut.leftDrop then .dropMinus else if x.cut.rightDrop then .dropPlus else .ordinary
    else .ordinary

def init (width height layer track : ℕ) : Fin 7 → ℤ :=
  ![width,height,layer,track,1000,1,-1]

def commonCode : List Instruction :=
  [⟨.add,1,1,5⟩,⟨.multiply,1,1,4⟩,⟨.add,0,0,5⟩,
   ⟨.add,0,0,5⟩,⟨.multiply,0,0,1⟩,⟨.add,2,2,2⟩]
def layerCode (m : Mode) : List Instruction :=
  (if m=.even then [] else [⟨.add,2,2,5⟩]) ++ [⟨.multiply,2,2,0⟩]
def offsetCode : Mode → List Instruction
  | .probe => []
  | .even => [⟨.add,3,3,5⟩,⟨.multiply,3,3,1⟩,⟨.add,2,2,3⟩]
  | .ordinary => [⟨.add,3,3,5⟩,⟨.multiply,3,3,1⟩,⟨.add,4,5,5⟩,
      ⟨.divide,1,1,4⟩,⟨.add,3,3,1⟩,⟨.add,2,2,3⟩]
  | .risePlus => [⟨.add,3,3,5⟩,⟨.add,3,3,5⟩,⟨.multiply,3,3,1⟩,
      ⟨.add,3,3,5⟩,⟨.add,2,2,3⟩]
  | .riseMinus => [⟨.add,3,3,5⟩,⟨.add,3,3,5⟩,⟨.multiply,3,3,1⟩,
      ⟨.add,3,3,6⟩,⟨.add,2,2,3⟩]
  | .dropPlus => [⟨.add,3,3,5⟩,⟨.multiply,3,3,1⟩,⟨.add,3,3,5⟩,⟨.add,2,2,3⟩]
  | .dropMinus => [⟨.add,3,3,5⟩,⟨.multiply,3,3,1⟩,⟨.add,3,3,6⟩,⟨.add,2,2,3⟩]
def code (m : Mode) : List Instruction := commonCode ++ layerCode m ++ offsetCode m

def offset (m : Mode) (δ : ℤ) (track : ℕ) : ℤ :=
  match m with
  | .probe => 0
  | .even => (track+1)*δ
  | .ordinary => (track+1)*δ+δ/2
  | .risePlus => (track+2)*δ+1
  | .riseMinus => (track+2)*δ-1
  | .dropPlus => (track+1)*δ+1
  | .dropMinus => (track+1)*δ-1

def value (m : Mode) (width height layer track : ℕ) : ℤ :=
  (2*(layer:ℤ)+(if m=.even then 0 else 1))*UnitInterval.commonLength width height+
    offset m (UnitInterval.scale height) track

lemma code_value (m : Mode) (width height layer track : ℕ) :
    evaluate (code m) (init width height layer track) 2=value m width height layer track := by
  cases m <;> simp [code,commonCode,layerCode,offsetCode,evaluate,Instruction.eval,Operation.eval,
    init,value,offset,UnitInterval.commonLength,UnitInterval.scale] <;> ring

lemma code_constants (m : Mode) (width height layer track : ℕ) :
    evaluate (code m) (init width height layer track) 5=1 ∧
    evaluate (code m) (init width height layer track) 6=-1 := by
  cases m <;> simp [code,commonCode,layerCode,offsetCode,evaluate,Instruction.eval,init]

lemma code_valid (m : Mode) (width height layer track : ℕ) :
    Valid (code m) (init width height layer track) := by
  cases m <;> simp [code,commonCode,layerCode,offsetCode,Valid,Operation.Valid,
    Instruction.eval,Operation.eval,init]
  exact ⟨500*((height:ℤ)+1),by ring⟩
end UnitBaseline

def offsetBase (δ : ℤ) (x : VertexRecord) : ℤ :=
  UnitBaseline.offset (UnitBaseline.mode x) δ x.track

namespace UnitBaseline
lemma mode_value (width height : ℕ) (x : VertexRecord) :
    value (mode x) width height x.layer x.track=
      if x.probe then (2*(x.layer:ℤ)+1)*UnitInterval.commonLength width height else
        (2*(x.layer:ℤ)+(if x.side then 1 else 0))*UnitInterval.commonLength width height+
          offsetBase (UnitInterval.scale height) x := by
  unfold offsetBase
  by_cases hp : x.probe=true
  · simp [mode,hp,value,offset]
  · by_cases hs : x.side=true
    · have hm : mode x≠.even := by simp [mode,hp,hs]; split_ifs <;> decide
      simp [value,hp,hs,hm]
    · simp [mode,hp,hs,value]
end UnitBaseline
end HiddenCircuits.GraphReduction.Runtime
