import HiddenCircuits.GraphReduction.Runtime.RecordParser
import HiddenCircuits.GraphReduction.Runtime.DirectedPredicate
import HiddenCircuits.GraphReduction.Runtime.LocalCleanup
import HiddenCircuits.Complexity.MatrixEmitterGraph

/-! Concrete register layout of the monotone structural-descriptor callback. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

structure QueryContext where
  n : ℕ
  row : ℕ
  col : ℕ
  descriptor : BitString
  out : BitString
  inner : BitString
  outer : BitString

def callbackStore (c : QueryContext) (bit rowData colData : BitString)
    (rowFields colFields : Fin 9 → BitString) (forward backward : BitString) : Store 56 :=
  fun i =>
    if i.val=0 then List.replicate c.n true else
    if i.val=1 then List.replicate c.row true else
    if i.val=2 then List.replicate c.col true else
    if i.val=3 then bit else
    if i.val=4 then c.out else
    if i.val=5 then c.inner else
    if i.val=6 then c.outer else
    if i.val=8 then c.descriptor else
    if i.val=9 then rowData else
    if i.val=10 then colData else
    if i.val=11 then rowFields 0 else
    if i.val=12 then rowFields 1 else
    if i.val=13 then rowFields 2 else
    if i.val=14 then rowFields 3 else
    if i.val=15 then rowFields 4 else
    if i.val=16 then rowFields 5 else
    if i.val=17 then rowFields 6 else
    if i.val=18 then rowFields 7 else
    if i.val=19 then rowFields 8 else
    if i.val=22 then colFields 0 else
    if i.val=23 then colFields 1 else
    if i.val=24 then colFields 2 else
    if i.val=25 then colFields 3 else
    if i.val=26 then colFields 4 else
    if i.val=27 then colFields 5 else
    if i.val=28 then colFields 6 else
    if i.val=29 then colFields 7 else
    if i.val=30 then colFields 8 else
    if i.val=33 then forward else
    if i.val=34 then backward else []

def callbackParams (descriptor : BitString) : Store 56 := fun i => if i.val=8 then descriptor else []

def queryContext (records : List VertexRecord) (i j : ℕ) (out inner outer : BitString) : QueryContext :=
  ⟨records.length,i,j,encodeBitList (records.map encodeVertex),out,inner,outer⟩

def defaultRecord : VertexRecord := ⟨false,false,0,0,backgroundCode⟩
def recordEdge (records : List VertexRecord) (i j : ℕ) : Bool :=
  recordAdj (records[i]?.getD defaultRecord) (records[j]?.getD defaultRecord)

def callbackBound (n L : ℕ) : ℕ := 2*lookupBound L n+1000*L+2500

def callbackRowLookupEmbedding : Fin 7 ↪ Fin 57 where
  toFun i := ![8,1,9,11,12,13,14] i
  inj' := by decide +kernel

def callbackColLookupEmbedding : Fin 7 ↪ Fin 57 where
  toFun i := ![8,2,10,11,12,13,14] i
  inj' := by decide +kernel

def callbackRowParseEmbedding : Fin 12 ↪ Fin 57 where
  toFun i := ![9,11,12,13,14,15,16,17,18,19,20,21] i
  inj' := by decide +kernel

def callbackColParseEmbedding : Fin 12 ↪ Fin 57 where
  toFun i := ![10,22,23,24,25,26,27,28,29,30,31,32] i
  inj' := by decide +kernel

def callbackForwardEmbedding : Fin 41 ↪ Fin 57 where
  toFun i := ![11,12,13,14,15,16,17,18,19,22,23,24,25,26,27,28,29,30,33,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56] i
  inj' := by decide +kernel

def callbackBackwardEmbedding : Fin 41 ↪ Fin 57 where
  toFun i := ![22,23,24,25,26,27,28,29,30,11,12,13,14,15,16,17,18,19,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56] i
  inj' := by decide +kernel

def callbackOrEmbedding : Fin 18 ↪ Fin 57 where
  toFun i := ![33,34,11,22,12,23,13,24,35,36,37,38,39,40,41,42,3,43] i
  inj' := by decide +kernel

noncomputable def callbackRowLookup : OracleBlock 56 := listLookupOn callbackRowLookupEmbedding
noncomputable def callbackColLookup : OracleBlock 56 := listLookupOn callbackColLookupEmbedding
noncomputable def callbackRowParse : OracleBlock 56 := rename recordParse callbackRowParseEmbedding
noncomputable def callbackColParse : OracleBlock 56 := rename recordParse callbackColParseEmbedding
noncomputable def callbackForward : OracleBlock 56 := directedPredicateOn callbackForwardEmbedding
noncomputable def callbackBackward : OracleBlock 56 := directedPredicateOn callbackBackwardEmbedding
noncomputable def callbackOr : OracleBlock 56 := gate8On callbackOrEmbedding orGate

def callbackWork : List (Fin 57) := [11,12,13,14,15,16,17,18,19,22,23,24,25,26,27,28,29,30,33,34]

noncomputable def callbackLookup : OracleBlock 56 := seq callbackRowLookup callbackColLookup
noncomputable def callbackParse : OracleBlock 56 := seq callbackRowParse callbackColParse
noncomputable def callbackEdges : OracleBlock 56 := seq callbackForward (seq callbackBackward callbackOr)
noncomputable def monotoneCallback : OracleBlock 56 :=
  seq callbackLookup (seq callbackParse (seq callbackEdges (clearList callbackWork)))

lemma callbackStore_initial (c : QueryContext) (bit : BitString) :
    callbackStore c bit [] [] (fun _ => []) (fun _ => []) [] [] =
      MatrixEmitter.store (k := 49) c.n c.row c.col bit c.out c.inner c.outer (callbackParams c.descriptor) := by
  funext i; fin_cases i <;> simp [callbackStore,MatrixEmitter.store,MatrixEmitter.port,callbackParams]

lemma descriptor_member_length {w : BitString} {ws : List BitString} (hw : w∈ws) :
    w.length≤(encodeBitList ws).length := by
  induction ws with
  | nil => simp at hw
  | cons x xs ih =>
    rcases List.mem_cons.mp hw with rfl|ht
    · simp [encodeBitList]; omega
    · have h := ih ht
      simp only [encodeBitList_length] at h
      simp [encodeBitList]; omega

lemma descriptor_record_length (records : List VertexRecord) (i : Fin records.length) :
    (encodeVertex (records.get i)).length≤(encodeBitList (records.map encodeVertex)).length :=
  descriptor_member_length (List.mem_map.mpr ⟨records.get i,List.get_mem _ _,rfl⟩)

end HiddenCircuits.GraphReduction.Runtime
