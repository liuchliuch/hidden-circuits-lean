import HiddenCircuits.GraphReduction.Runtime.RecordRestrictions

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

set_option maxHeartbeats 1600000 in
theorem recordLayerParse_executes (g : BitString → ℕ) (v : VertexRecord) :
    recordLayerParse.Executes g (recordStage1 v) (recordStage2 v) (5*v.layer+3) := by
  have htime : 5*(List.replicate v.layer true).length+3=5*v.layer+3 := by simp
  have h := rename_executes_to CNFCloneEmitter.ClauseLookup.parseOne recordLayerEmbedding g
    (outerS := recordStage1 v) (outerT := recordStage2 v)
    (CNFCloneEmitter.ClauseLookup.parseOne_executes g [v.side] (List.replicate v.layer true) (pairBits (List.replicate v.track true) (List.replicate v.cut.index true)))
    (layerInputRestriction v) (layerOutputRestriction v) (layerOutsideFrame v)
  exact Eq.mp (congrArg (fun t => recordLayerParse.Executes g (recordStage1 v) (recordStage2 v) t) htime) h

theorem recordLayer_clear (g : BitString → ℕ) (v : VertexRecord) :
    (clear (11 : Fin 12)).Executes g (recordStage2 v) (recordStage3 v) 2 :=
  clear_executes g (11 : Fin 12) (recordStage2 v)

end HiddenCircuits.GraphReduction.Runtime
