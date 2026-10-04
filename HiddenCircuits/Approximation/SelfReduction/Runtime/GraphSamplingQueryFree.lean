import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSamplingStage
import HiddenCircuits.Approximation.SelfReduction.Runtime.StageQueryFree

/-! Query-free audit for the concrete general-graph sampling stage. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
open Complexity Complexity.OracleBlock

theorem partnerRequests_queryFree : partnerRequests.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ requestGenerator_queryFree)
    (rename_queryFree _ _ partnerBatch_queryFree)

 theorem sampleGroupBody_queryFree : sampleGroupBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ partnerRequests_queryFree) (emitWordReversed_queryFree _ _))
 theorem sampleGroupLoop_queryFree : sampleGroupLoop.QueryFree :=
  whilePop_queryFree _ _ _ sampleGroupBody_queryFree sampleGroupBody_queryFree
 theorem sampleGroups_queryFree : sampleGroups.QueryFree :=
  seq_queryFree _ _ sampleGroupLoop_queryFree (reverseOn_queryFree _ _ _)
 theorem stage_queryFree : stage.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ sampleGroups_queryFree)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (push_queryFree _ _)
          (seq_queryFree _ _ (rename_queryFree _ _ branchSelect_queryFree) (clear_queryFree _)))))

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
