import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderPrepare

namespace HiddenCircuits.GraphReduction.Runtime.MonotonePermutationOrderRuntime
open MonotoneOrderRuntime
open Complexity OracleBlock
set_option maxHeartbeats 800000

def localGate (lower : Bool) : List Bool → Bool
  | [ls,rs,lp,rp,f,b,trackLT,trackGT] =>
    if lower then
      if lp then
        if ls then rp && rs && trackLT
        else if rp && !rs then trackLT else true
      else if rp then rs
      else if ls==rs then trackGT
      else if ls then b else !f
    else
      if lp then rp && (if ls==rs then trackLT else ls)
      else if rp then true
      else if ls==rs then trackGT
      else if ls then b else !f
  | _ => false

def finalGate : List Bool → Bool
  | [lt,eq,localBit,_,_,_,_,_] => lt || (eq && localBit)
  | _ => false
noncomputable def localBlock (lower : Bool) : OracleBlock 56 := gate8On localEmbedding (localGate lower)
noncomputable def finalBlock : OracleBlock 56 := gate8On finalEmbedding finalGate
noncomputable def boolean (lower : Bool) : OracleBlock 56 := seq (localBlock lower) finalBlock

lemma localBlock_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    (localBlock lower).Executes g (state lower c x y 6) (state lower c x y 7) 92 := by
  let bits : Fin 8 → Bool := ![x.side,y.side,x.probe,y.probe,PrivateCut.cut lower x y,PrivateCut.cut lower y x,decide (x.track<y.track),decide (y.track<x.track)]
  have hc:=gate8On_executes localEmbedding g (localGate lower) bits (state lower c x y 6) (by funext i;fin_cases i <;> rfl)
  have he:localGate lower (gate8Args bits)=localValue lower x y:=by
    cases lower <;> simp [localGate,localValue,bits,gate8Args,PrivateCut.cut,MonotoneOrder.upperLocalLT,MonotoneOrder.lowerLocalLT]
  rw [he] at hc
  convert hc using 1
  funext i;fin_cases i <;> rfl

lemma finalBlock_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    finalBlock.Executes g (state lower c x y 7) (state lower c x y 7 [orderValue lower x y]) 92 := by
  let bits : Fin 8 → Bool := ![decide (layerValue lower x<layerValue lower y),decide (layerValue lower x=layerValue lower y),localValue lower x y,
    x.side,y.side,x.probe,y.probe,PrivateCut.cut lower x y]
  have hc:=gate8On_executes finalEmbedding g finalGate bits (state lower c x y 7) (by funext i;fin_cases i <;> rfl)
  have he:finalGate (gate8Args bits)=orderValue lower x y:=by
    cases lower <;> simp [orderValue,finalGate,gate8Args,bits,orderValue,localValue,layerValue,MonotoneLayer.value,MonotoneOrder.lowerLayer,MonotoneOrder.upperRecordLT,MonotoneOrder.lowerRecordLT]
  rw [he] at hc
  convert hc using 1
  funext i;fin_cases i <;> rfl
lemma boolean_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    (boolean lower).Executes g (state lower c x y 6) (state lower c x y 7 [orderValue lower x y]) 186 :=
  seq_executes _ _ g (localBlock_executes g lower c x y) (finalBlock_executes g lower c x y)
lemma boolean_queryFree (lower : Bool) : (boolean lower).QueryFree := seq_queryFree _ _ (gate8On_queryFree _ _) (gate8On_queryFree _ _)
end HiddenCircuits.GraphReduction.Runtime.MonotonePermutationOrderRuntime
