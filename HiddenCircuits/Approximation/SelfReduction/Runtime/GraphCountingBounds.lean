import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingStage
import HiddenCircuits.Approximation.SelfReduction.Runtime.StageBounds
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphResidualPolynomial

/-! Uniform graph, request, matrix and literal-stage bounds, on every tape. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity SelfReduction.GraphCount

def graphBound (b : ℕ) : ℕ := (b+2)^2
def contextBound (b T : ℕ) : ℕ := 2*graphBound b+T+1
def matrixBound (b T h : ℕ) : ℕ := 2*(2*h+1+1)*(2*batchSize T*(b+2)+1)
noncomputable def stageBound (b m T h : ℕ) : ℕ :=
  GraphSampling.stageBound (contextBound b T) b (2*h+1) m (batchSize T) (b+1) (8*T) (matrixBound b T h)

lemma graph_length {b n : ℕ} (G : MatrixGraph n) (hG : n≤b+1) :
    (GraphInput.encode ⟨n,G⟩).length≤graphBound b := by
  simp only [GraphInput.encode,pairBits_length,List.length_replicate,MatrixGraph.bits_length]
  unfold graphBound
  have hh := Nat.pow_le_pow_left hG 2
  nlinarith

lemma context_length {b d : ℕ} (G : MatrixGraph (2*d)) (hG : 2*d≤b+1) (T : ℕ) :
    (sampleInput (stateBytes (b:=b) ⟨d,some ⟨G,hG⟩⟩) T).length≤contextBound b T := by
  rw [sampleInput_length]
  have hh := graph_length G hG
  change 2*(GraphInput.encode ⟨2*d,G⟩).length+T+1≤_
  unfold contextBound
  omega

lemma stageBound_sound {b d : ℕ} (G : MatrixGraph (2*(d+1))) (hG : 2*(d+1)≤b+1)
    (m T h : ℕ) (r : StageTape (CoinTape m) T h) :
    GraphSampling.stageBound (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩) T).length
      b (2*h+1) m (batchSize T) (b+1) (8*T)
      (groupWords (List.ofFn (sampleMatrix b T h (sample T m ⟨d+1,some ⟨G,hG⟩⟩) r))).length≤
      stageBound b m T h :=
  GraphSampling.stageBound_mono _ _ _ _ _ _ _ _ _ _ (context_length G hG T)
    (Runtime.sampleMatrix_length b T h _ r)

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
