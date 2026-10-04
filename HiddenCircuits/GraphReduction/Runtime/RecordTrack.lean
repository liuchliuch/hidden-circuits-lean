import HiddenCircuits.GraphReduction.Runtime.RecordRestrictions

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

set_option maxHeartbeats 1600000 in
theorem recordTrackParse_executes (g : BitString → ℕ) (v : VertexRecord) :
    recordTrackParse.Executes g (recordStage3 v) (recordStage4 v) (5*v.track+3) := by
  have htime : 5*(List.replicate v.track true).length+3=5*v.track+3 := by simp
  have h := rename_executes_to CNFCloneEmitter.ClauseLookup.parseOne recordTrackEmbedding g
    (outerS := recordStage3 v) (outerT := recordStage4 v)
    (CNFCloneEmitter.ClauseLookup.parseOne_executes g [v.side] (List.replicate v.track true) (List.replicate v.cut.index true))
    (trackInputRestriction v) (trackOutputRestriction v) (trackOutsideFrame v)
  exact Eq.mp (congrArg (fun t => recordTrackParse.Executes g (recordStage3 v) (recordStage4 v) t) htime) h

theorem recordTrack_clear (g : BitString → ℕ) (v : VertexRecord) :
    (clear (11 : Fin 12)).Executes g (recordStage4 v) (recordStage5 v) 2 :=
  clear_executes g (11 : Fin 12) (recordStage4 v)

end HiddenCircuits.GraphReduction.Runtime
