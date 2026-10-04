import HiddenCircuits.Approximation.SelfReduction.Runtime.RobustSelect
import HiddenCircuits.Approximation.SelfReduction.Runtime.MatchTallyLoop
import HiddenCircuits.Approximation.SelfReduction.Runtime.CoinBlocks

/-! The counting compiler's actual blocks contain no oracle instruction. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

 theorem maxBody_queryFree : maxBody.QueryFree := by
  have hp : maxParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have hc : maxCompare.QueryFree := readUnaryLeOn_queryFree _
  have hr : maxReplace.QueryFree := seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (clear_queryFree _) (copyOn_queryFree _ _ _ _ _ _)))
  have hd : maxDecision.QueryFree := branchPop_queryFree _ _ _ _ (clear_queryFree _) (clear_queryFree _) hr
  exact seq_queryFree _ _ hp (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ hc (seq_queryFree _ _ hd (push_queryFree _ _))))

 theorem maximumScan_queryFree : maximumScan.QueryFree :=
  whilePop_queryFree _ _ _ skip_queryFree maxBody_queryFree

 theorem clusterBody_queryFree : clusterBody.QueryFree := by
  have hp : clusterParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have ht : clusterTest.QueryFree := rename_queryFree _ _ radiusTest_queryFree
  have hi : clusterIncrement.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (push_queryFree _ _)
  exact seq_queryFree _ _ hp (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ ht (seq_queryFree _ _ hi (clear_queryFree _))))

 theorem neighborhoodScan_queryFree : neighborhoodScan.QueryFree :=
  whilePop_queryFree _ _ _ skip_queryFree clusterBody_queryFree

 theorem robustBody_queryFree : robustBody.QueryFree := by
  have hp : robustParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have hs : robustScan.QueryFree := rename_queryFree _ _ neighborhoodScan_queryFree
  exact seq_queryFree _ _ hp (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ hs (seq_queryFree _ _ (emitUnaryReversed_queryFree _ _) (clear_queryFree _)))))

 theorem robustScores_queryFree : robustScores.QueryFree :=
  seq_queryFree _ _ (whilePop_queryFree _ _ _ skip_queryFree robustBody_queryFree) (reverseOn_queryFree _ _ _)

 theorem robustSelectScores_queryFree : robustSelectScores.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ robustScores_queryFree (seq_queryFree _ _ (clear_queryFree _)
      (rename_queryFree _ _ maximumScan_queryFree)))

 theorem listLookup_queryFree : listLookup.QueryFree := by
  have hp : listParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have hd : discardParsed.QueryFree := seq_queryFree _ _ hp
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))
  have hw : discardWord.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree hd
  have hr : retainParsed.QueryFree := seq_queryFree _ _ hp
    (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))
  have hk : retainWord.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree hr
  exact seq_queryFree _ _ (whilePop_queryFree _ _ _ hw hw) hk

 theorem robustSelect_queryFree : robustSelect.QueryFree :=
  seq_queryFree _ _ robustSelectScores_queryFree
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _)
      (rename_queryFree _ _ listLookup_queryFree)))

 theorem matchBody_queryFree : matchBody.QueryFree := by
  have hp : matchParse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
  have hc : matchCompare.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (push_queryFree _ _) (rename_queryFree _ _ CNFCloneEmitter.WordEquality.program_queryFree)))
  have hi : matchIncrement.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (push_queryFree _ _)
  exact seq_queryFree _ _ hp (seq_queryFree _ _ (clear_queryFree _)
    (seq_queryFree _ _ hc (seq_queryFree _ _ hi (clear_queryFree _))))

 theorem occurrenceTally_queryFree : occurrenceTally.QueryFree :=
  whilePop_queryFree _ _ _ skip_queryFree matchBody_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime
