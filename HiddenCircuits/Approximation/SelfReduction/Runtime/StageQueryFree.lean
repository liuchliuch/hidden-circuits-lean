import HiddenCircuits.Approximation.SelfReduction.Runtime.SamplingStage
import HiddenCircuits.Approximation.SelfReduction.Runtime.ContextPrepare
import HiddenCircuits.Approximation.SelfReduction.Runtime.QueryFree

/-! The complete sampling/counting stage contains no oracle instruction. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock

 theorem requestBody_queryFree : requestBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ takeCoins_queryFree)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (pairEmit_queryFree _ _ _ _ _) (emitWordReversed_queryFree _ _))))
 theorem requestGenerator_queryFree : requestGenerator.QueryFree :=
  seq_queryFree _ _ (whilePop_queryFree _ _ _ requestBody_queryFree requestBody_queryFree)
    (reverseOn_queryFree _ _ _)
 theorem partnerRequests_queryFree : partnerRequests.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ requestGenerator_queryFree) (rename_queryFree _ _ partnerBatch_queryFree)
 theorem groupBody_queryFree : groupBody.QueryFree :=
  seq_queryFree _ _ (GraphVerifier.Runtime.unpairOn_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _
      (rename_queryFree _ _ occurrenceTally_queryFree) (emitUnaryReversed_queryFree _ _)))
 theorem groupCounts_queryFree : groupCounts.QueryFree :=
  seq_queryFree _ _ (whilePop_queryFree _ _ _ skip_queryFree groupBody_queryFree) (reverseOn_queryFree _ _ _)
 theorem groupBoost_queryFree : groupBoost.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ groupCounts_queryFree)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ robustSelect_queryFree)))
 theorem branchBoostBody_queryFree : branchBoostBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ groupBoost_queryFree)
      (seq_queryFree _ _ (emitUnaryReversed_queryFree _ _) (push_queryFree _ _)))
 theorem branchBoostLoop_queryFree : branchBoostLoop.QueryFree :=
  whilePop_queryFree _ _ _ branchBoostBody_queryFree branchBoostBody_queryFree
 theorem branchFinalize_queryFree : branchFinalize.QueryFree :=
  seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (reverseOn_queryFree _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ maximumScan_queryFree) (clear_queryFree _)))
 theorem branchSelect_queryFree : branchSelect.QueryFree :=
  seq_queryFree _ _ branchBoostLoop_queryFree branchFinalize_queryFree
 theorem sampleGroupBody_queryFree : sampleGroupBody.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ partnerRequests_queryFree) (emitWordReversed_queryFree _ _))
 theorem sampleGroupLoop_queryFree : sampleGroupLoop.QueryFree :=
  whilePop_queryFree _ _ _ sampleGroupBody_queryFree sampleGroupBody_queryFree
 theorem sampleGroups_queryFree : sampleGroups.QueryFree :=
  seq_queryFree _ _ sampleGroupLoop_queryFree (reverseOn_queryFree _ _ _)
 theorem samplingStage_queryFree : samplingStage.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ sampleGroups_queryFree)
      (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
        (seq_queryFree _ _ (push_queryFree _ _)
          (seq_queryFree _ _ (rename_queryFree _ _ branchSelect_queryFree) (clear_queryFree _)))))

end HiddenCircuits.Approximation.SelfReduction.Runtime
