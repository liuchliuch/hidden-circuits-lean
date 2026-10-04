import HiddenCircuits.Approximation.SelfReduction.Runtime.CountLoopSuccess
import HiddenCircuits.Approximation.SamplerRuntime.CoinLists

/-! Exact flattening of the entire adaptive finite experiment into the physical
coin stack, with no additional or ideal random source. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity

 theorem countingStageBytes_countingTapes (m T h d : ℕ) (r : CoinTape (countingBits m T h d)) :
    countingStageBytes m T h d (countingTapes m T h d r)=List.ofFn r := by
  have hs (i : Fin d) : stageBytes m T h (countingTapes m T h d r i)=
      List.ofFn (splitBlocks d (2*(h+1)*(batchSize T*m)) r i) := by
    simpa only [stageBytes,countingTapes,Equiv.trans_apply,Equiv.piCongrRight_apply] using
      stageCoinBlocks_flatten m T h (splitBlocks d (2*(h+1)*(batchSize T*m)) r i)
  unfold countingStageBytes
  simp_rw [hs]
  exact ofFn_splitBlocks _ _ r

 theorem countingBits_le_global (m T h d N : ℕ) (hd : d ≤ N) :
    countingBits m T h d ≤ countingBits m T h N := by
  unfold countingBits
  exact Nat.mul_le_mul_right _ hd

end HiddenCircuits.Approximation.SelfReduction.Runtime
