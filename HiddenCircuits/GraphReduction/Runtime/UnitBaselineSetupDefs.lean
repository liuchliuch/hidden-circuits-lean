import HiddenCircuits.GraphReduction.Runtime.UnitBaselineRuntime
import HiddenCircuits.GraphReduction.Runtime.UnarySignedRead
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackDefs

/-! Physically parsed descriptor fields and the signed arithmetic bank. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetup
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic RegisterMachine

def magnitude (width height : ℕ) (x : VertexRecord) : ℕ :=
  width+height+x.layer+x.track+x.cut.index+1002

def state (c : QueryContext) (width height : ℕ) (data : BitString)
    (fields : Fin 9 → BitString) (numbers : Fin 7 → BitString) (equal : BitString) : Store 95 := fun i=>
  if i.val=0 then List.replicate c.n true else
  if i.val=1 then List.replicate c.row true else
  if i.val=2 then List.replicate c.col true else
  if i.val=4 then c.out else if i.val=5 then c.inner else if i.val=6 then c.outer else
  if i.val=8 then c.descriptor else if i.val=9 then data else
  if i.val=17 then fields 6 else if i.val=18 then fields 7 else if i.val=19 then fields 8 else
  if i.val=57 then List.replicate width true else if i.val=58 then List.replicate height true else
  if i.val=60 then fields 2 else if i.val=61 then fields 4 else
  if i.val=62 then fields 3 else if i.val=63 then fields 5 else
  if i.val=76 then fields 0 else if i.val=77 then fields 1 else if i.val=78 then equal else
  if h : 89 ≤ i.val then numbers ⟨i.val-89,by omega⟩ else []

def initial (c : QueryContext) (width height : ℕ) : Store 95 :=
  state c width height [] (fun _=>[]) (fun _=>[]) []
def parsed (c : QueryContext) (width height : ℕ) (x : VertexRecord) : Store 95 :=
  state c width height [] (recordFields x) (fun _=>[]) []
def ready (c : QueryContext) (width height : ℕ) (x : VertexRecord) : Store 95 :=
  state c width height [] (recordFields x) (signedBits ∘ UnitBaseline.init width height x.layer x.track)
    [decide (x.track=x.cut.index)]
def result (c : QueryContext) (width height : ℕ) (x : VertexRecord) (R : Fin 7 → ℤ) : Store 95 :=
  state c width height [] (fun i=>if i=1 then [x.probe] else []) (signedBits ∘ R) []

def lookupMap : Fin 7 ↪ Fin 96 where
  toFun i := ![8,1,9,20,21,22,23] i
  inj' := by decide +kernel
def parseMap : Fin 12 ↪ Fin 96 where
  toFun i := ![9,76,77,60,62,61,63,17,18,19,20,21] i
  inj' := by decide +kernel
def readMap (i : Fin 4) : Fin 4 ↪ Fin 96 where
  toFun j := ![(![57,58,17,18] i),(⟨89+i.val,by omega⟩ : Fin 96),80,81] j
  inj' := by fin_cases i <;> decide +kernel
def equalMap : Fin 6 ↪ Fin 96 where
  toFun i := ![18,19,78,80,81,82] i
  inj' := by decide +kernel
def arithmeticMap : Fin 23 ↪ Fin 96 where
  toFun i := if h : i.val < 16 then ⟨80+i.val,by omega⟩ else
    ![77,76,78,60,61,62,63] ⟨i.val-16,by omega⟩
  inj' := by decide +kernel

noncomputable def lookup : OracleBlock 95 := listLookupOn lookupMap
noncomputable def parse : OracleBlock 95 := rename recordParse parseMap
noncomputable def readNumbers : OracleBlock 95 :=
  seq (UnarySignedRead.on (readMap 0)) (seq (UnarySignedRead.on (readMap 1))
    (seq (UnarySignedRead.on (readMap 2)) (UnarySignedRead.on (readMap 3))))
noncomputable def equal : OracleBlock 95 := Complexity.GraphVerifier.Runtime.readLengthOn equalMap
/-- LSB-first magnitude for 1000, plus sign; also the exact constants 1 and -1. -/
def constantFlags : List (Fin 96 × Bool) :=
  ((signedBits 1000).reverse.map (fun b=>(93,b))) ++
  ((signedBits 1).reverse.map (fun b=>(94,b))) ++
  ((signedBits (-1)).reverse.map (fun b=>(95,b)))
noncomputable def seed : OracleBlock 95 := seedFlags constantFlags
noncomputable def setup : OracleBlock 95 := seq readNumbers (seq equal seed)
noncomputable def arithmetic : OracleBlock 95 := rename UnitBaseline.program arithmeticMap
def cleanPorts : List (Fin 96) := [17,18,19,60,61,62,63,76,78]
noncomputable def clean : OracleBlock 95 := clearList cleanPorts

end HiddenCircuits.GraphReduction.Runtime.UnitBaselineSetup
