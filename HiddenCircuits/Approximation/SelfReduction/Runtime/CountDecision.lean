import HiddenCircuits.Approximation.SelfReduction.Runtime.CountPrimitives
import HiddenCircuits.Approximation.SelfReduction.Runtime.StageBounds

/-! The observed zero/nonzero test is a literal bit pop. Positive factors are
restored before serialization and endpoint deletion; zero factors stop early. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock
open GraphReduction.MonotoneEndpointEncoding
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

 theorem naturalAmplifiedCount_le {α : Type*} (E : α → Prop) [DecidablePred E]
    (T h : ℕ) (r : StageTape α T h) : naturalAmplifiedCount E T h r ≤ batchSize T := by
  unfold naturalAmplifiedCount eventCount
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

 theorem countDecision_zero (g : BitString → ℕ) (coins context graph : BitString)
    (width batch T cap groups depth idx : ℕ) (out : BitString) :
    countDecision.Executes g (countStore coins context graph width batch T cap groups depth out [true] 0 idx)
      (countStore coins [] graph width batch T cap groups 0 out [] 0 0)
      (depth+idx+context.length+13) := by
  apply branchPop_empty _ _ _ _ g rfl
  exact countReject_executes g coins context graph width batch T cap groups depth idx out

 theorem countDecision_positive (g : BitString → ℕ) {d : ℕ} (E : MonotoneEndpoints (d+1)) (j : Fin (d+1))
    (coins context : BitString) (width batch T cap groups depth c : ℕ) (hc : 0 < c) (out : BitString) :
    ∃ t, countDecision.Executes g
      (countStore coins context (encode ⟨d+1,E⟩) width batch T cap groups depth out [true] c j.val)
      (countStore coins [] (encode ⟨d,SamplerRuntime.EndpointFiber.deleteFirst E j⟩) width batch T cap groups depth
        ((true::pairBits (List.replicate c true) []).reverse++out) [true] 0 0) t ∧
      t ≤ 1000*(d+2)^2+9*c+j.val+context.length+20 := by
  obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
  obtain ⟨t,ht,hb⟩ := countAccept_executes g E j coins context width batch T cap groups depth c out
  have hpop : Function.update
      (countStore coins context (encode ⟨d+1,E⟩) width batch T cap groups depth out [true] (c+1) j.val)
      (7 : Fin 71) (List.replicate c true)=
      countStore coins context (encode ⟨d+1,E⟩) width batch T cap groups depth out [true] c j.val := by
    funext i; fin_cases i <;> rfl
  refine ⟨t+2,?_,by omega⟩
  apply branchPop_true _ _ _ _ g (rest:=List.replicate c true) (by rfl)
  rw [hpop]
  exact ht

 theorem countStage_executes (g : BitString → ℕ) {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (m T h depth : ℕ) (r : StageTape (CoinTape m) T h) (rest out : BitString) :
    let s : SelfReduction.EndpointResidual.State b := ⟨d+1,some ⟨E,hE⟩⟩
    let graph := stateBytes s
    let context := sampleInput graph T
    let j := naturalSelectedBranch b T h (sample T m) s r
    let c := naturalAmplifiedCount (fun a => sample T m s a=some j) T h r
    ∃ t, countStage.Executes g
      (countStore ((List.ofFn (stageCoinBlocks m T h r)).flatten.flatten++rest) context graph m (batchSize T) T (b+1)
        (2*h+1+1) depth out [true] 0 0)
      (countStore rest context graph m (batchSize T) T (b+1) (2*h+1+1) depth out [true] c j.val) t ∧
      t ≤ endpointStageBound b m T h := by
  dsimp only
  obtain ⟨t,ht,hb⟩ := endpointStage_executes g E hE m T h r rest
  refine ⟨t,?_,hb.trans (endpointStageBound_sound E hE m T h r)⟩
  exact countFrame_rename g _ _ _ ht (stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩) T depth out [true]

end HiddenCircuits.Approximation.SelfReduction.Runtime
