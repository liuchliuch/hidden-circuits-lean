import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointStage

/-! Uniform explicit polynomial envelopes for every residual stage. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity
open HiddenCircuits.Approximation.SelfReduction.EndpointResidual

 def endpointGraphBound (b : ℕ) : ℕ := 8*(b+1)^2+10*(b+1)+6
 def endpointContextBound (b T : ℕ) : ℕ := 2*endpointGraphBound b+T+1
 def endpointMatrixBound (b T h : ℕ) : ℕ := 2*(2*h+1+1)*(2*batchSize T*(b+2)+1)
 noncomputable def endpointStageBound (b m T h : ℕ) : ℕ :=
   samplingStageBound (endpointContextBound b T) b (2*h+1) m (batchSize T) (b+1) (8*T)
     (endpointMatrixBound b T h)

 theorem endpointGraph_length {b d : ℕ} (E : MonotoneEndpoints d) (hE : d ≤ b+1) :
    (GraphReduction.MonotoneEndpointEncoding.encode ⟨d,E⟩).length ≤ endpointGraphBound b := by
  apply (GraphReduction.MonotoneEndpointEncoding.encode_length ⟨d,E⟩).trans
  dsimp only [endpointGraphBound]
  gcongr

 theorem endpointContext_length {b d : ℕ} (E : MonotoneEndpoints d) (hE : d ≤ b+1) (T : ℕ) :
    (sampleInput (stateBytes (b:=b) ⟨d,some ⟨E,hE⟩⟩) T).length ≤ endpointContextBound b T := by
  rw [sampleInput_length]
  have h := endpointGraph_length E hE
  change 2*(GraphReduction.MonotoneEndpointEncoding.encode ⟨d,E⟩).length+T+1 ≤ _
  unfold endpointContextBound
  omega

 theorem sampleMatrix_length {α : Type*} (b T h : ℕ) (sample : α → Option (Fin (b+1)))
    (r : StageTape α T h) :
    (groupWords (List.ofFn (sampleMatrix b T h sample r))).length ≤ endpointMatrixBound b T h := by
  apply (groupWords_length_bound (List.ofFn (sampleMatrix b T h sample r)) (batchSize T) (b+1) ?_ ?_).trans_eq
  · simp only [List.length_ofFn,endpointMatrixBound]
  · intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simp [sampleMatrix]
  · intro xs hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    intro x hx; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact encodePartner_length _

 theorem samplingStageBound_mono (C C' b n m M B radius L L' : ℕ) (hC : C ≤ C') (hL : L ≤ L') :
    samplingStageBound C b n m M B radius L ≤ samplingStageBound C' b n m M B radius L' := by
  dsimp only [samplingStageBound,sampleGroupBound,branchIterationBound]
  gcongr
  exact polynomial_nat_eval_mono _ (by omega)

 theorem endpointStageBound_sound {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1 ≤ b+1)
    (m T h : ℕ) (r : StageTape (CoinTape m) T h) :
    samplingStageBound (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩) T).length
      b (2*h+1) m (batchSize T) (b+1) (8*T)
      (groupWords (List.ofFn (sampleMatrix b T h (sample T m ⟨d+1,some ⟨E,hE⟩⟩) r))).length ≤
      endpointStageBound b m T h :=
  samplingStageBound_mono _ _ _ _ _ _ _ _ _ _ (endpointContext_length E hE T)
    (sampleMatrix_length b T h _ r)

end HiddenCircuits.Approximation.SelfReduction.Runtime
