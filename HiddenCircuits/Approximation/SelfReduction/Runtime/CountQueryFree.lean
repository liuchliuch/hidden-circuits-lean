import HiddenCircuits.Approximation.SelfReduction.Runtime.CountFrame
import HiddenCircuits.Approximation.SelfReduction.Runtime.StageQueryFree

/-! The complete adaptive counting loop has no oracle instruction. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock
 theorem countPrepare_queryFree : countPrepare.QueryFree := rename_queryFree _ _ contextPrepare_queryFree
 theorem countStage_queryFree : countStage.QueryFree := rename_queryFree _ _ samplingStage_queryFree
 theorem countResidual_queryFree : countResidual.QueryFree := EndpointResidual.programOn_queryFree _
 theorem countAccept_queryFree : countAccept.QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (emitUnaryReversed_queryFree _ _)
    (seq_queryFree _ _ countResidual_queryFree (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
 theorem countReject_queryFree : countReject.QueryFree :=
  seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _)))
 theorem countDecision_queryFree : countDecision.QueryFree :=
  branchPop_queryFree _ _ _ _ countReject_queryFree countAccept_queryFree countAccept_queryFree
 theorem countBody_queryFree : countBody.QueryFree :=
  seq_queryFree _ _ countPrepare_queryFree (seq_queryFree _ _ countStage_queryFree countDecision_queryFree)
 theorem countLoop_queryFree : countLoop.QueryFree := whilePop_queryFree _ _ _ countBody_queryFree countBody_queryFree
end HiddenCircuits.Approximation.SelfReduction.Runtime
