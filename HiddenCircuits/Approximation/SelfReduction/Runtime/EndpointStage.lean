import HiddenCircuits.Approximation.SelfReduction.Runtime.SamplingStage
import HiddenCircuits.Approximation.SelfReduction.Runtime.BranchStatistics
import HiddenCircuits.Approximation.SelfReduction.Runtime.CoinSlices
import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualSampler
import HiddenCircuits.Approximation.SelfReduction.ObservedSoundness

/-! The actual complete stage specialized to the concrete endpoint sampler.
Every produced byte agrees with the exact typed finite counting experiment. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

 theorem endpointMatrix_eq {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (m T h : ℕ) (r : StageTape (CoinTape m) T h) (i : Fin (2*h+1+1)) :
    sampledWords (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩) T) (stageCoinBlocks m T h r i)=
      sampleMatrix b T h (sample T m ⟨d+1,some ⟨E,hE⟩⟩) r i := by
  simp only [sampledWords,stageCoinBlocks,sampleMatrix,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext j
  exact sample_active_bytes E hE T m _

 theorem endpointStage_executes (g : BitString → ℕ) {b d : ℕ} (E : MonotoneEndpoints (d+1))
    (hE : d+1 ≤ b+1) (m T h : ℕ) (r : StageTape (CoinTape m) T h) (rest : BitString) :
    let s : SelfReduction.EndpointResidual.State b := ⟨d+1,some ⟨E,hE⟩⟩
    let context := sampleInput (stateBytes s) T
    let j := naturalSelectedBranch b T h (sample T m) s r
    let c := naturalAmplifiedCount (fun a => sample T m s a=some j) T h r
    ∃ t, samplingStage.Executes g
      (stageStore ((List.ofFn (stageCoinBlocks m T h r)).flatten.flatten++rest) context m (batchSize T)
        (8*T) (b+1) (2*h+1+1) 0 [] 0 0)
      (stageStore rest context m (batchSize T) (8*T) (b+1) (2*h+1+1) 0 [] c j.val) t ∧
      t ≤ samplingStageBound context.length b (2*h+1) m (batchSize T) (b+1) (8*T)
        (groupWords (List.ofFn (sampleMatrix b T h (sample T m s) r))).length := by
  dsimp only
  have hB (i) : ∀ word ∈ sampledWords (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩) T)
      (stageCoinBlocks m T h r i), word.length ≤ b+1 := by
    rw [endpointMatrix_eq E hE]
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact encodePartner_length _
  have ht := samplingStage_executes g (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩) T) rest
    b (2*h+1) m (batchSize T) (b+1) (8*T) (stageCoinBlocks m T h r)
    (stageCoinBlocks_length m T h r) (stageCoinBlocks_width m T h r) hB
  dsimp only at ht
  simp only [endpointMatrix_eq E hE,branchBoostValue_statistical,naturalSelectedBranch] at ht ⊢
  exact ht

/-- The empirical stage's positive value certifies a legal positive-count child
on every coin tape, even if the probabilistic approximation event fails. -/
theorem endpointStage_positive {b : ℕ} (m T h : ℕ) (s : SelfReduction.EndpointResidual.State b) (r : StageTape (CoinTape m) T h)
    (hp : 0 < naturalAmplifiedCount
      (fun a => sample T m s a=some (naturalSelectedBranch b T h (sample T m) s r)) T h r) :
    0 < count (child s (naturalSelectedBranch b T h (sample T m) s r)) := by
  obtain ⟨a,ha⟩ := naturalAmplifiedCount_positive _ T h r hp
  exact sample_sound T m s a _ ha

end HiddenCircuits.Approximation.SelfReduction.Runtime
