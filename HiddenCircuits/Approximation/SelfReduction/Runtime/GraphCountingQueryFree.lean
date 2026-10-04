import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingBody
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSamplingQueryFree

/-! No general-graph counter instruction is an oracle query. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock
lemma prepare_queryFree : prepare.QueryFree := rename_queryFree _ _ countPrepare_queryFree
lemma reject_queryFree : reject.QueryFree := rename_queryFree _ _ countReject_queryFree
lemma stage_queryFree : stage.QueryFree := rename_queryFree _ _ GraphSampling.stage_queryFree
lemma acceptSmall_queryFree : acceptSmall.QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (emitUnaryReversed_queryFree _ _)
    (seq_queryFree _ _ (GraphResidual.programOn_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))))
lemma accept_queryFree : accept.QueryFree := rename_queryFree _ _ acceptSmall_queryFree
lemma decision_queryFree : decision.QueryFree := branchPop_queryFree _ _ _ _ reject_queryFree accept_queryFree accept_queryFree
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ prepare_queryFree (seq_queryFree _ _ stage_queryFree decision_queryFree)
lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree
lemma finish_queryFree : finish.QueryFree := rename_queryFree _ _ countFinish_queryFree
end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
