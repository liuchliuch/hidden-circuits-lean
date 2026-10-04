import HiddenCircuits.GraphReduction.Runtime.RecordFieldsParser

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

noncomputable def recordParse : OracleBlock 11 := seq recordPrefixParse
  (seq recordLayerParse (seq (clear 11) (seq recordTrackParse (seq (clear 11) (reverseOn 0 9 (by decide))))))

theorem recordParse_executes (g : BitString → ℕ) (v : VertexRecord) :
    recordParse.Executes g (recordParseStore (encodeVertex v) (fun _ => []) [] [])
      (recordParseStore [] (recordFields v) [] []) (5*v.layer+5*v.track+2*v.cut.index+49) := by
  convert seq_executes _ _ g (recordPrefix_ready g v)
    (seq_executes _ _ g (recordLayerParse_executes g v)
      (seq_executes _ _ g (recordLayer_clear g v)
        (seq_executes _ _ g (recordTrackParse_executes g v)
          (seq_executes _ _ g (recordTrack_clear g v) (recordIndexParse_executes g v))))) using 1 <;> omega

lemma recordParse_cost_le (v : VertexRecord) :
    5*v.layer+5*v.track+2*v.cut.index+49 ≤ 5*(encodeVertex v).length+9 := by
  rw [encodeVertex_length]; omega

lemma recordParse_queryFree : recordParse.QueryFree := by
  have hp : recordPrefixParse.QueryFree :=
    seq_queryFree _ _ (readBit_queryFree _ _) (seq_queryFree _ _ (readBit_queryFree _ _) (seq_queryFree _ _ (readBit_queryFree _ _) (seq_queryFree _ _ (readBit_queryFree _ _) (seq_queryFree _ _ (readBit_queryFree _ _) ((readBit_queryFree _ _))))))
  exact seq_queryFree _ _ hp
    (seq_queryFree _ _ (rename_queryFree _ _ CNFCloneEmitter.ClauseLookup.parseOne_queryFree)
      (seq_queryFree _ _ (clear_queryFree _)
        (seq_queryFree _ _ (rename_queryFree _ _ CNFCloneEmitter.ClauseLookup.parseOne_queryFree)
          (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))))

end HiddenCircuits.GraphReduction.Runtime
