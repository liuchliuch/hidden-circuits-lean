import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphDefs
import HiddenCircuits.GraphReduction.Runtime.RawWordLookup
import HiddenCircuits.GraphReduction.Runtime.IntegerDistanceRuntime

namespace HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def params (data : BitString) (d : ℤ) : Store 31 := fun i=>
  if i.val=8 then data else if i.val=9 then signedBits d else []
def callbackState (n i j : ℕ) (out inner outer data : BitString) (d : ℤ) : Store 31 :=
  MatrixEmitter.store n i j [] out inner outer (params data d)
def lookupMap (second : Bool) : Fin 7 ↪ Fin 32 where
  toFun i := if i.val=0 then 8 else if i.val=1 then (if second then 2 else 1)
    else if i.val=2 then (if second then 12 else 11) else ⟨i.val+24,by omega⟩
  inj' := by cases second <;> decide +kernel
def normalizeMap (second : Bool) : Fin 4 ↪ Fin 32 where
  toFun i := if i.val=0 then (if second then 12 else 11) else ⟨i.val+26,by omega⟩
  inj' := by cases second <;> decide +kernel
def distanceMap : Fin 17 ↪ Fin 32 where
  toFun i:=⟨i.val+10,by omega⟩
  inj':=by intro i j h;apply Fin.ext;have:=congrArg Fin.val h;dsimp at this;omega
def equalMap : Fin 6 ↪ Fin 32 where
  toFun i:=![1,2,31,27,28,29] i
  inj':=by decide +kernel
noncomputable def lookup (second : Bool) : OracleBlock 31 := listLookupOn (lookupMap second)
noncomputable def normalize (second : Bool) : OracleBlock 31 := SignedNormalize.on (normalizeMap second)
noncomputable def copyD : OracleBlock 31 := copyOn 9 10 27 (by decide) (by decide) (by decide)
noncomputable def distance : OracleBlock 31 := rename IntegerDistance.program distanceMap
noncomputable def equal : OracleBlock 31 := Complexity.GraphVerifier.Runtime.readLengthOn equalMap
noncomputable def gate : OracleBlock 31 := Complexity.GraphVerifier.Runtime.decision 3 [13,31]
  (fun bs=>(bs[0]?.getD false)&& !(bs[1]?.getD true))
noncomputable def callback : OracleBlock 31 := seq (lookup false) (seq (normalize false)
  (seq (lookup true) (seq (normalize true) (seq copyD (seq distance (seq equal gate))))))
noncomputable def callbackBound (n L D : ℕ) : ℕ :=
  2*rawLookupBound L n+20*L+30*n+IntegerDistance.time.eval (L+D+3)+5*D+150

lemma lookup_length (data : BitString) (i : ℕ) : ((LooseWordList.words data)[i]?.getD []).length≤data.length := by
  cases h:(LooseWordList.words data)[i]? with
  | none => simp [h]
  | some w => exact LooseWordList.word_length data w (List.mem_of_getElem? h)
lemma endpoint_length (data : BitString) (i : ℕ) : (signedBits (endpoint data i)).length≤data.length+1 :=
  (SignedNormalize.signed_length _).trans (by have h:=lookup_length data i;omega)
end HiddenCircuits.GraphReduction.Runtime.CoordinateGraph
