import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingDecision
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountBody

/-! Every physical iteration is bounded, even on statistically bad tapes.
Only a positive observed factor licenses the legal residual transition. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity Complexity.OracleBlock SelfReduction.GraphCount

noncomputable def body : OracleBlock 106 := seq prepare (seq stage decision)
noncomputable def loop : OracleBlock 106 := whilePop 67 body body
noncomputable def choice {b : ℕ} (m T h : ℕ) (s : SelfReduction.GraphCount.State b)
    (r : StageTape (CoinTape m) T h) : Fin (b+1) := naturalSelectedBranch b T h (sample T m) s r
noncomputable def value {b : ℕ} (m T h : ℕ) (s : SelfReduction.GraphCount.State b)
    (r : StageTape (CoinTape m) T h) : ℕ :=
  naturalAmplifiedCount (fun a => sample T m s a=some (choice m T h s r)) T h r
noncomputable def bodyBound (b m T h : ℕ) : ℕ :=
  5*T+13*graphBound b+stageBound b m T h+
    GraphResidual.timeBound (b+1)+9*batchSize T+2*b+contextBound b T+50

 theorem body_zero (g : BitString → ℕ) {b d : ℕ} (G : MatrixGraph (2*(d+1))) (hG : 2*(d+1)≤b+1)
    (m T h originalDepth N : ℕ) (r : StageTape (CoinTape m) T h) (rest out : BitString)
    (hz : value m T h ⟨d+1,some ⟨G,hG⟩⟩ r=0) :
    let graph := stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩
    ∃t,body.Executes g
      (store (coreStore (countStore (stageBytes m T h r++rest) [] graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0) originalDepth N))
      (store (coreStore (countStore rest [] graph m (batchSize T) T (b+1) (2*h+1+1) 0 out [] 0 0) originalDepth N)) t ∧
      t≤bodyBound b m T h := by
  dsimp only
  let graph := stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩
  let context := sampleInput graph T
  let j := choice m T h ⟨d+1,some ⟨G,hG⟩⟩ r
  have hp := prepare_executes g (stageBytes m T h r++rest) graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] originalDepth N
  obtain ⟨ts,hs,hbs⟩ := graphStage_executes g G hG m T h d originalDepth N r rest out
  have hbs' := hbs.trans (stageBound_sound G hG m T h r)
  change stage.Executes g _ (store (coreStore (countStore rest context graph m (batchSize T) T (b+1) (2*h+1+1) d out [true]
    (value m T h ⟨d+1,some ⟨G,hG⟩⟩ r) j.val) originalDepth N)) ts at hs
  rw [hz] at hs
  have hd := decision_zero g rest context graph m (batchSize T) T (b+1) (2*h+1+1) d j.val out originalDepth N
  have hgraph := graph_length G hG
  have hcontext := context_length G hG T
  have hj := j.isLt
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hs hd),?_⟩
  change _≤bodyBound b m T h
  dsimp only [bodyBound,graph,context,stateBytes] at *
  omega

 theorem body_positive (g : BitString → ℕ) {b d : ℕ} (G : MatrixGraph (2*(d+1))) (hG : 2*(d+1)≤b+1)
    (m T h originalDepth N : ℕ) (r : StageTape (CoinTape m) T h) (rest out : BitString)
    (hc : 0<value m T h ⟨d+1,some ⟨G,hG⟩⟩ r) :
    let s : SelfReduction.GraphCount.State b := ⟨d+1,some ⟨G,hG⟩⟩
    let graph := stateBytes s
    let j := choice m T h s r
    let c := value m T h s r
    ∃t,body.Executes g
      (store (coreStore (countStore (stageBytes m T h r++rest) [] graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] 0 0) originalDepth N))
      (store (coreStore (countStore rest [] (stateBytes (child s j)) m (batchSize T) T (b+1) (2*h+1+1) d
        ((true::pairBits (List.replicate c true) []).reverse++out) [true] 0 0) originalDepth N)) t ∧
      t≤bodyBound b m T h := by
  dsimp only
  let s : SelfReduction.GraphCount.State b := ⟨d+1,some ⟨G,hG⟩⟩
  let graph := stateBytes s
  let context := sampleInput graph T
  let j := choice m T h s r
  let c := value m T h s r
  have hpos : 0<count (child s j) := chosenCount_child_positive T m T h s r hc
  have hlegal := positive_child_legal G hG j hpos
  let j' : Fin (2*(d+1)) := ⟨j.val,hlegal.1⟩
  have hbytes : stateBytes (child s j)=GraphResidual.output G j' := by
    rw [child_legal G hG j hlegal.1 hlegal.2,GraphResidual.output_as_evenGraph G j' hlegal.2.ne.symm]
    rfl
  have hp := prepare_executes g (stageBytes m T h r++rest) graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] originalDepth N
  obtain ⟨ts,hs,hbs⟩ := graphStage_executes g G hG m T h d originalDepth N r rest out
  have hbs' := hbs.trans (stageBound_sound G hG m T h r)
  obtain ⟨td,hd,hbd⟩ := decision_positive g (n:=2*d+1) G j' rest context m (batchSize T) T (b+1) (2*h+1+1) d c originalDepth N hc out
  have hd' : decision.Executes g
      (store (coreStore (countStore rest context graph m (batchSize T) T (b+1) (2*h+1+1) d out [true] c j.val) originalDepth N))
      (store (coreStore (countStore rest [] (stateBytes (child s j)) m (batchSize T) T (b+1) (2*h+1+1) d
        ((true::pairBits (List.replicate c true) []).reverse++out) [true] 0 0) originalDepth N)) td := by
    rw [hbytes]
    exact hd
  have hgraph := graph_length G hG
  have hcontext := context_length G hG T
  have hcount : c≤batchSize T := naturalAmplifiedCount_le _ T h r
  have hj := j.isLt
  have hdim : GraphResidual.timeBound (2*d+1+1)≤GraphResidual.timeBound (b+1) :=
    GraphResidual.timeBound_mono (by omega)
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hs hd'),?_⟩
  change _≤bodyBound b m T h
  dsimp only [bodyBound,graph,context,s,j',c,j,stateBytes] at *
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
