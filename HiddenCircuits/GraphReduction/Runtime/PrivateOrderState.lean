import HiddenCircuits.GraphReduction.Runtime.PrivateCut
import HiddenCircuits.GraphReduction.Runtime.PrivateLayer
import HiddenCircuits.GraphReduction.Runtime.PrivateOrderDefs
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallback

namespace HiddenCircuits.GraphReduction.Runtime.PrivateOrderRuntime
open Complexity OracleBlock

def layerValue (lower : Bool) (x : VertexRecord) := PrivateLayer.value lower x.side x.layer
def localValue (lower : Bool) (x y : VertexRecord) := if lower then PrivateOrder.lowerLocalLT x y else PrivateOrder.upperLocalLT x y
def orderValue (lower : Bool) (x y : VertexRecord) := if lower then PrivateOrder.lowerRecordLT x y else PrivateOrder.upperRecordLT x y
def flags (lower : Bool) (x y : VertexRecord) : Fin 7 → BitString :=
  ![List.replicate (layerValue lower x) true,List.replicate (layerValue lower y) true,
    [decide (layerValue lower x<layerValue lower y)],[decide (layerValue lower x=layerValue lower y)],
    [decide (x.track<y.track)],[decide (y.track<x.track)],[localValue lower x y]]
def state (lower : Bool) (c : QueryContext) (x y : VertexRecord) (stage : ℕ) (output : BitString := []) : Store 56 := fun i =>
  if h:35≤ i.val ∧ i.val<42 then if i.val-35<stage then flags lower x y ⟨i.val-35,by omega⟩ else []
  else callbackStore c output [] [] (recordFields x) (recordFields y) [PrivateCut.cut lower x y] [PrivateCut.cut lower y x] i

def xLayerEmbedding : Fin 5 ↪ Fin 57 where
  toFun i := (![17,11,35,51,52] : Fin 5 → Fin 57) i
  inj' := by decide +kernel
def yLayerEmbedding : Fin 5 ↪ Fin 57 where
  toFun i := (![28,22,36,51,52] : Fin 5 → Fin 57) i
  inj' := by decide +kernel
def layerLTEmbedding : Fin 6 ↪ Fin 57 where
  toFun i := (![35,36,37,42,43,44] : Fin 6 → Fin 57) i
  inj' := by decide +kernel
def layerEQEmbedding : Fin 6 ↪ Fin 57 where
  toFun i := (![35,36,38,42,43,44] : Fin 6 → Fin 57) i
  inj' := by decide +kernel
def trackLTEmbedding : Fin 6 ↪ Fin 57 where
  toFun i := (![18,29,39,42,43,44] : Fin 6 → Fin 57) i
  inj' := by decide +kernel
def trackGTEmbedding : Fin 6 ↪ Fin 57 where
  toFun i := (![29,18,40,42,43,44] : Fin 6 → Fin 57) i
  inj' := by decide +kernel

def localEmbedding : Fin 18 ↪ Fin 57 where
  toFun i := (![11,22,12,23,33,34,39,40,42,43,44,45,46,47,48,49,41,50] : Fin 18 → Fin 57) i
  inj' := by decide +kernel
def finalEmbedding : Fin 18 ↪ Fin 57 where
  toFun i := (![37,38,41,11,22,12,23,33,42,43,44,45,46,47,48,49,3,50] : Fin 18 → Fin 57) i
  inj' := by decide +kernel

lemma layerValue_le (lower : Bool) (x : VertexRecord) : layerValue lower x≤x.layer+1 := by
  unfold layerValue PrivateLayer.value
  split_ifs <;> omega
lemma state_zero (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    state lower c x y 0=callbackStore c [] [] [] (recordFields x) (recordFields y) [PrivateCut.cut lower x y] [PrivateCut.cut lower y x] := by
  funext i;fin_cases i <;> rfl
end HiddenCircuits.GraphReduction.Runtime.PrivateOrderRuntime
