import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountControlStage
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSampler
import HiddenCircuits.Approximation.SelfReduction.Runtime.BranchStatistics
import HiddenCircuits.Approximation.SelfReduction.Runtime.CoinSlices

/-! Sample and tally bytes agree on every tape with the
analyzed state-indexed general-graph counting experiment. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity
open SelfReduction.GraphCount

lemma graphMatrix_eq {b d : ℕ} (G : MatrixGraph (2*(d+1))) (hG : 2*(d+1)≤b+1)
    (m T h : ℕ) (r : StageTape (CoinTape m) T h) (i : Fin (2*h+1+1)) :
    GraphSampling.sampledWords (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩) T)
        (stageCoinBlocks m T h r i)=
      sampleMatrix b T h (sample T m ⟨d+1,some ⟨G,hG⟩⟩) r i := by
  simp only [GraphSampling.sampledWords,stageCoinBlocks,sampleMatrix,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext j
  exact sample_active_bytes G hG T m _

theorem graphStage_executes (g : BitString → ℕ) {b d : ℕ} (G : MatrixGraph (2*(d+1)))
    (hG : 2*(d+1)≤b+1) (m T h depth originalDepth N : ℕ)
    (r : StageTape (CoinTape m) T h) (rest out : BitString) :
    let s : SelfReduction.GraphCount.State b := ⟨d+1,some ⟨G,hG⟩⟩
    let graph := stateBytes s
    let context := sampleInput graph T
    let j := naturalSelectedBranch b T h (sample T m) s r
    let c := naturalAmplifiedCount (fun a => sample T m s a=some j) T h r
    ∃t,stage.Executes g
      (store (coreStore (countStore ((List.ofFn (stageCoinBlocks m T h r)).flatten.flatten++rest)
        context graph m (batchSize T) T (b+1) (2*h+1+1) depth out [true] 0 0) originalDepth N))
      (store (coreStore (countStore rest context graph m (batchSize T) T (b+1) (2*h+1+1)
        depth out [true] c j.val) originalDepth N)) t ∧
      t≤GraphSampling.stageBound context.length b (2*h+1) m (batchSize T) (b+1) (8*T)
        (groupWords (List.ofFn (sampleMatrix b T h (sample T m s) r))).length := by
  dsimp only
  have hB (i) : ∀word∈GraphSampling.sampledWords
      (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩) T) (stageCoinBlocks m T h r i),word.length≤b+1 := by
    rw [graphMatrix_eq G hG]
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact encodePartner_length _
  have ht := stage_executes g (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩) T) rest
    (stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩) out [true] b (2*h+1) m (batchSize T) (b+1)
    T depth originalDepth N (stageCoinBlocks m T h r)
    (stageCoinBlocks_length m T h r) (stageCoinBlocks_width m T h r) hB
  dsimp only at ht
  simp only [graphMatrix_eq G hG,branchBoostValue_statistical,naturalSelectedBranch] at ht ⊢
  exact ht
end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
