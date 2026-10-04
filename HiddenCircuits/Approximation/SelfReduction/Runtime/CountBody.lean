import HiddenCircuits.Approximation.SelfReduction.Runtime.CountDecision

/-! Every literal deletion iteration is bounded, including statistically bad
samples. Only the observed positive count allows residual construction. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity Complexity.OracleBlock
open GraphReduction.MonotoneEndpointEncoding
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

 def countChoice {b : ℕ} (m T h : ℕ) (s : SelfReduction.EndpointResidual.State b)
    (r : StageTape (CoinTape m) T h) : Fin (b+1) := naturalSelectedBranch b T h (sample T m) s r
 def countValue {b : ℕ} (m T h : ℕ) (s : SelfReduction.EndpointResidual.State b)
    (r : StageTape (CoinTape m) T h) : ℕ :=
  naturalAmplifiedCount (fun a => sample T m s a=some (countChoice m T h s r)) T h r
 def stageBytes (m T h : ℕ) (r : StageTape (CoinTape m) T h) : BitString :=
  (List.ofFn (stageCoinBlocks m T h r)).flatten.flatten

noncomputable def countBodyBound (b m T h : ℕ) : ℕ :=
  5*T+13*endpointGraphBound b+endpointStageBound b m T h+
    1000*(b+2)^2+9*batchSize T+2*b+endpointContextBound b T+50

 theorem countBody_zero (g : BitString → ℕ) {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (m T h : ℕ) (r : StageTape (CoinTape m) T h) (rest out : BitString)
    (hz : countValue m T h ⟨d+1,some ⟨E,hE⟩⟩ r=0) :
    let graph := stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩
    ∃ t, countBody.Executes g
      (countStore (stageBytes m T h r++rest) [] graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (countStore rest [] graph m (batchSize T) T (b+1) (2*h+1+1) 0 out [] 0 0) t ∧
      t ≤ countBodyBound b m T h := by
  dsimp only
  let graph := stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩
  let context := sampleInput graph T
  let j := countChoice m T h ⟨d+1,some ⟨E,hE⟩⟩ r
  have hp := countPrepare_executes g (stageBytes m T h r++rest) graph m (batchSize T) T (b+1) (2*h+1+1) d out [true]
  obtain ⟨ts,hs,hbs⟩ := countStage_executes g E hE m T h d r rest out
  change countValue m T h ⟨d+1,some ⟨E,hE⟩⟩ r=0 at hz
  change countStage.Executes g _ (countStore rest context graph m (batchSize T) T (b+1) (2*h+1+1) d out [true]
    (countValue m T h ⟨d+1,some ⟨E,hE⟩⟩ r) j.val) ts at hs
  rw [hz] at hs
  have hd := countDecision_zero g rest context graph m (batchSize T) T (b+1) (2*h+1+1) d j.val out
  have hgraph := endpointGraph_length E hE
  have hcontext := endpointContext_length E hE T
  have hj := j.isLt
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hs hd),?_⟩
  change _ ≤ countBodyBound b m T h
  dsimp only [countBodyBound,graph,context,stateBytes] at *
  omega

 theorem countBody_positive (g : BitString → ℕ) {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (m T h : ℕ) (r : StageTape (CoinTape m) T h) (rest out : BitString)
    (hc : 0 < countValue m T h ⟨d+1,some ⟨E,hE⟩⟩ r) :
    let s : SelfReduction.EndpointResidual.State b := ⟨d+1,some ⟨E,hE⟩⟩
    let graph := stateBytes s
    let j := countChoice m T h s r
    let c := countValue m T h s r
    ∃ t, countBody.Executes g
      (countStore (stageBytes m T h r++rest) [] graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0)
      (countStore rest [] (stateBytes (child s j)) m (batchSize T) T (b+1) (2*h+1+1) d
        ((true::pairBits (List.replicate c true) []).reverse++out) [true] 0 0) t ∧
      t ≤ countBodyBound b m T h := by
  dsimp only
  let s : SelfReduction.EndpointResidual.State b := ⟨d+1,some ⟨E,hE⟩⟩
  let graph := stateBytes s
  let context := sampleInput graph T
  let j := countChoice m T h s r
  let c := countValue m T h s r
  have hpos : 0 < count (child s j) := endpointStage_positive m T h s r hc
  have hlegal := positive_child_legal E hE j hpos
  let j' : Fin (d+1) := ⟨j.val,hlegal.1⟩
  have hbytes : stateBytes (child s j)=encode ⟨d,SamplerRuntime.EndpointFiber.deleteFirst E j'⟩ := by
    rw [child_legal E hE j hlegal.1 hlegal.2]
    rfl
  have hp := countPrepare_executes g (stageBytes m T h r++rest) graph m (batchSize T) T (b+1) (2*h+1+1) d out [true]
  obtain ⟨ts,hs,hbs⟩ := countStage_executes g E hE m T h d r rest out
  obtain ⟨td,hd,hbd⟩ := countDecision_positive g E j' rest context m (batchSize T) T (b+1) (2*h+1+1) d c hc out
  have hd' : countDecision.Executes g (countStore rest context graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] c j.val)
      (countStore rest [] (stateBytes (child s j)) m (batchSize T) T (b+1) (2*h+1+1) d
        ((true::pairBits (List.replicate c true) []).reverse++out) [true] 0 0) td := by
    rw [hbytes]
    exact hd
  have hgraph := endpointGraph_length E hE
  have hcontext := endpointContext_length E hE T
  have hcount : c ≤ batchSize T := naturalAmplifiedCount_le _ T h r
  have hj := j.isLt
  have hdim : 1000*(d+2)^2 ≤ 1000*(b+2)^2 := by gcongr; omega
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hs hd'),?_⟩
  change _ ≤ countBodyBound b m T h
  dsimp only [countBodyBound,graph,context,s,j',c,j,stateBytes] at *
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
