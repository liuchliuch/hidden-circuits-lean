import HiddenCircuits.GraphReduction.Runtime.UnitCorrectionPredicate
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackLookup
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackParse
import HiddenCircuits.GraphReduction.Runtime.SignedScanDefs

namespace HiddenCircuits.GraphReduction.Runtime.UnitSignedCallback
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

def params (width height : ℕ) (descriptor : BitString) : Store 95 := fun i=>
  if i.val=8 then descriptor else if i.val=57 then List.replicate width true else
  if i.val=58 then List.replicate height true else []
def bound (n L width : ℕ) : ℕ := 2*lookupBound L n+3000*L+1000*width+10000

def frame (base : Store 56) (width height : ℕ) (R : Fin 7 → ℤ) : Store 95 := fun i=>
  if h:i.val<57 then base ⟨i.val,h⟩ else
  if i.val=57 then List.replicate width true else if i.val=58 then List.replicate height true else
  if h : 80 ≤ i.val then RegisterMachine.store [] [] (signedBits ∘ R) ⟨i.val-80,by omega⟩ else []

def lowMap : Fin 57 ↪ Fin 96 where
  toFun i:=⟨i.val,by omega⟩
  inj':=by intro i j h;exact Fin.ext (congrArg (fun q:Fin 96=>q.val) h)

def predicateMap : Fin 49 ↪ Fin 96 where
  toFun i := if h:i.val<9 then ⟨11+i.val,by omega⟩ else
    if h:i.val<18 then ⟨13+i.val,by omega⟩ else
    if i.val=18 then 57 else if i.val=19 then 3 else if i.val=20 then 59 else
    if i.val=21 then 64 else if h:i.val<45 then ⟨11+i.val,by omega⟩ else ⟨20+i.val,by omega⟩
  inj':=by decide +kernel

def cleanPorts : List (Fin 96) := [11,12,13,14,15,16,17,18,19,22,23,24,25,26,27,28,29,30]
noncomputable def lookup : OracleBlock 95 := rename callbackLookup lowMap
noncomputable def parse : OracleBlock 95 := rename callbackParse lowMap
noncomputable def predicate (second : Bool) : OracleBlock 95 := UnitCorrection.on predicateMap second
noncomputable def program (second : Bool) : OracleBlock 95 := seq lookup (seq parse (seq (predicate second) (clearList cleanPorts)))

lemma frame_executes (B : OracleBlock 56) (g : BitString → ℕ) (s t : Store 56) (a width height : ℕ)
    (R : Fin 7 → ℤ) (h:B.Executes g s t a) :
    (rename B lowMap).Executes g (frame s width height R) (frame t width height R) a := by
  apply rename_executes_to _ lowMap g h
  · funext i;simp [frame,lowMap,i.isLt]
  · funext i;simp [frame,lowMap,i.isLt]
  · intro i hi
    have hn : ¬i.val<57 := by intro h;exact hi ⟨i.val,h⟩ (Fin.ext rfl)
    simp [frame,hn]

lemma initial_eq (c : QueryContext) (width height : ℕ) (R : Fin 7 → ℤ) (bit : BitString) :
    frame (callbackStore c bit [] [] (fun _=>[]) (fun _=>[]) [] []) width height R=
      SignedScan.state c.n c.row c.col bit c.out c.inner c.outer (params width height c.descriptor) R := by
  funext i;fin_cases i <;> rfl
end HiddenCircuits.GraphReduction.Runtime.UnitSignedCallback
