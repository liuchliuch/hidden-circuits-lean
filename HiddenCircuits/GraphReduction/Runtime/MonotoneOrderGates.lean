import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderPrepare

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
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

def finalGate (rightPart isLeft : Bool) : List Bool → Bool
  | [lt,eq,localBit,ls,rs,_,_,_] => if isLeft then !rs else (if rightPart then ls else !ls) && (lt || (eq && localBit))
  | _ => false
noncomputable def localBlock (lower : Bool) : OracleBlock 56 := gate8On localEmbedding (localGate lower)
noncomputable def finalBlock (rightPart isLeft : Bool) : OracleBlock 56 := gate8On finalEmbedding (finalGate rightPart isLeft)
noncomputable def boolean (lower rightPart isLeft : Bool) : OracleBlock 56 := seq (localBlock lower) (finalBlock rightPart isLeft)

lemma localBlock_executes (g : BitString→ℕ) (lower : Bool) (c : QueryContext) (x y : VertexRecord) :
    (localBlock lower).Executes g (state lower c x y 6) (state lower c x y 7) 92 := by
  let bits : Fin 8 → Bool := ![x.side,y.side,x.probe,y.probe,PrivateCut.cut lower x y,PrivateCut.cut lower y x,decide (x.track<y.track),decide (y.track<x.track)]
  have hc:=gate8On_executes localEmbedding g (localGate lower) bits (state lower c x y 6) (by funext i;fin_cases i <;> rfl)
  have he:localGate lower (gate8Args bits)=localValue lower x y:=by
    cases lower <;> simp [localGate,localValue,bits,gate8Args,PrivateCut.cut,MonotoneOrder.upperLocalLT,MonotoneOrder.lowerLocalLT]
  rw [he] at hc
  convert hc using 1
  funext i;fin_cases i <;> rfl

lemma finalBlock_executes (g : BitString→ℕ) (lower rightPart isLeft : Bool) (c : QueryContext) (x y : VertexRecord) :
    (finalBlock rightPart isLeft).Executes g (state lower c x y 7) (state lower c x y 7 [outputValue lower rightPart isLeft x y]) 92 := by
  let bits : Fin 8 → Bool := ![decide (layerValue lower x<layerValue lower y),decide (layerValue lower x=layerValue lower y),localValue lower x y,
    x.side,y.side,x.probe,y.probe,PrivateCut.cut lower x y]
  have hc:=gate8On_executes finalEmbedding g (finalGate rightPart isLeft) bits (state lower c x y 7) (by funext i;fin_cases i <;> rfl)
  have he:finalGate rightPart isLeft (gate8Args bits)=outputValue lower rightPart isLeft x y:=by
    cases lower <;> simp [outputValue,finalGate,gate8Args,bits,orderValue,localValue,layerValue,MonotoneLayer.value,MonotoneOrder.lowerLayer,MonotoneOrder.upperRecordLT,MonotoneOrder.lowerRecordLT]
  rw [he] at hc
  convert hc using 1
  funext i;fin_cases i <;> rfl
lemma boolean_executes (g : BitString→ℕ) (lower rightPart isLeft : Bool) (c : QueryContext) (x y : VertexRecord) :
    (boolean lower rightPart isLeft).Executes g (state lower c x y 6) (state lower c x y 7 [outputValue lower rightPart isLeft x y]) 186 :=
  seq_executes _ _ g (localBlock_executes g lower c x y) (finalBlock_executes g lower rightPart isLeft c x y)
lemma boolean_queryFree (lower rightPart isLeft : Bool) : (boolean lower rightPart isLeft).QueryFree := seq_queryFree _ _ (gate8On_queryFree _ _) (gate8On_queryFree _ _)
end HiddenCircuits.GraphReduction.Runtime.MonotoneOrderRuntime
