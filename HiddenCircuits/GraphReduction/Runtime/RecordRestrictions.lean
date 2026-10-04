import HiddenCircuits.GraphReduction.Runtime.RecordStages

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

lemma layerInputRestriction (v : VertexRecord) :
    recordStage1 v ∘ recordLayerEmbedding = CNFCloneEmitter.ClauseLookup.store
      (pairBits (List.replicate v.layer true) (pairBits (List.replicate v.track true) (List.replicate v.cut.index true))) [v.side] [] [] [] := by
  funext i; fin_cases i <;> rfl
lemma layerOutputRestriction (v : VertexRecord) :
    recordStage2 v ∘ recordLayerEmbedding = CNFCloneEmitter.ClauseLookup.store
      (pairBits (List.replicate v.track true) (List.replicate v.cut.index true)) [v.side] (List.replicate v.layer true) [] [true] := by
  funext i; fin_cases i <;> rfl
lemma layerOutsideFrame (v : VertexRecord) (i : Fin 12) (hi : ∀ j, recordLayerEmbedding j≠i) :
    recordStage2 v i=recordStage1 v i := by
  have h11 : i≠(11 : Fin 12) := (hi 4).symm
  have hout : i≠(7 : Fin 12) := (hi 2).symm
  have h0 : i≠(0 : Fin 12) := (hi 0).symm
  unfold recordStage2
  rw [Function.update_of_ne h11,Function.update_of_ne hout,Function.update_of_ne h0]

lemma trackInputRestriction (v : VertexRecord) :
    recordStage3 v ∘ recordTrackEmbedding = CNFCloneEmitter.ClauseLookup.store
      (pairBits (List.replicate v.track true) (List.replicate v.cut.index true)) [v.side] [] [] [] := by
  funext i; fin_cases i <;> rfl
lemma trackOutputRestriction (v : VertexRecord) :
    recordStage4 v ∘ recordTrackEmbedding = CNFCloneEmitter.ClauseLookup.store
      (List.replicate v.cut.index true) [v.side] (List.replicate v.track true) [] [true] := by
  funext i; fin_cases i <;> rfl
lemma trackOutsideFrame (v : VertexRecord) (i : Fin 12) (hi : ∀ j, recordTrackEmbedding j≠i) :
    recordStage4 v i=recordStage3 v i := by
  have h11 : i≠(11 : Fin 12) := (hi 4).symm
  have hout : i≠(8 : Fin 12) := (hi 2).symm
  have h0 : i≠(0 : Fin 12) := (hi 0).symm
  unfold recordStage4
  rw [Function.update_of_ne h11,Function.update_of_ne hout,Function.update_of_ne h0]

end HiddenCircuits.GraphReduction.Runtime
