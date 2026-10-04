import HiddenCircuits.GraphReduction.Runtime.RecordPrefix

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

def recordLayerEmbedding : Fin 5 ↪ Fin 12 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 1 else if i.val=2 then 7 else if i.val=3 then 10 else 11
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
def recordTrackEmbedding : Fin 5 ↪ Fin 12 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 1 else if i.val=2 then 8 else if i.val=3 then 10 else 11
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
noncomputable def recordLayerParse : OracleBlock 11 := rename CNFCloneEmitter.ClauseLookup.parseOne recordLayerEmbedding
noncomputable def recordTrackParse : OracleBlock 11 := rename CNFCloneEmitter.ClauseLookup.parseOne recordTrackEmbedding

def recordStage1 (v : VertexRecord) := recordParseStore (recordTail v) (prefixFields v 6) [] []
def recordStage2 (v : VertexRecord) : Store 11 :=
  Function.update (Function.update (Function.update (recordStage1 v) 0
    (pairBits (List.replicate v.track true) (List.replicate v.cut.index true))) 7
    (List.replicate v.layer true)) 11 [true]
def recordStage3 (v : VertexRecord) : Store 11 := Function.update (recordStage2 v) 11 []
def recordStage4 (v : VertexRecord) : Store 11 :=
  Function.update (Function.update (Function.update (recordStage3 v) 0
    (List.replicate v.cut.index true)) 8 (List.replicate v.track true)) 11 [true]
def recordStage5 (v : VertexRecord) : Store 11 := Function.update (recordStage4 v) 11 []

theorem recordPrefix_ready (g : BitString → ℕ) (v : VertexRecord) :
    recordPrefixParse.Executes g (recordParseStore (encodeVertex v) (fun _ => []) [] []) (recordStage1 v) 28 := by
  exact recordPrefixParse_executes g v


end HiddenCircuits.GraphReduction.Runtime
