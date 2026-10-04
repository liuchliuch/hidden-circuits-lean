import HiddenCircuits.Circuit.Runtime.SpectralNodes
import HiddenCircuits.Circuit.Runtime.SpectralOmissionCorrectness

namespace HiddenCircuits.Circuit.Runtime.SpectralFrontend
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial LagrangeIntegerArrays

def state (g j : ℕ) (roots value : BitString) : Store 13 := fun i =>
  if i.val=0 then roots else if i.val=2 then value else if i.val=12 then List.replicate g true
  else if i.val=13 then List.replicate j true else []
def nodesEmbedding : Fin 13 ↪ Fin 14 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h;apply Fin.ext;exact congrArg (fun z : Fin 14 => z.val) h⟩
def omitEmbedding : Fin 8 ↪ Fin 14 :=
  ⟨fun i => ⟨i.val,by omega⟩,by intro i j h;apply Fin.ext;exact congrArg (fun z : Fin 14 => z.val) h⟩
noncomputable def nodes : OracleBlock 13 := rename SpectralNodes.program nodesEmbedding
noncomputable def eraseNode : OracleBlock 13 := rename SpectralNodeOmission.program omitEmbedding
noncomputable def program : OracleBlock 13 := seq nodes
  (seq (copyOn 13 1 9 (by decide) (by decide) (by decide)) (seq eraseNode (clear 1)))
noncomputable def streamBound : Polynomial ℕ := (X+1)^2*(2*(4*(X+1)+2)+2)
noncomputable def time : Polynomial ℕ := SpectralNodes.time+100*(streamBound+(X+1)^2+1)^2+6*(X+1)^2+9

theorem program_executes (oracle : BitString → ℕ) (g j : ℕ) (hj : j<(spectralIndices g).length) :
    ∃t, program.Executes oracle (state g j [] [])
      (state g j (encodeBitList ((otherNodes (spectralIndices g) spectralIntegerNode (spectralIndices g)[j]).map signedBits))
        (signedBits (spectralIntegerNode (spectralIndices g)[j]))) t ∧ t≤time.eval g := by
  let words := ((spectralIndices g).map spectralIntegerNode).map signedBits
  let others := (otherNodes (spectralIndices g) spectralIntegerNode (spectralIndices g)[j]).map signedBits
  let value := signedBits (spectralIntegerNode (spectralIndices g)[j])
  let s₁ := state g j (encodeBitList words) []
  let s₂ := Function.update s₁ (1:Fin 14) (List.replicate j true)
  let s₃ := Function.update (state g j (encodeBitList others) value) (1:Fin 14) (List.replicate j true)
  obtain ⟨a,ha,hab⟩ := SpectralNodes.program_executes oracle g
  have h₁ : nodes.Executes oracle (state g j [] []) s₁ a := by
    apply rename_executes_to SpectralNodes.program nodesEmbedding oracle ha
    · funext i;fin_cases i <;> simp [state,nodesEmbedding,SpectralNodes.inputStore]
    · funext i;fin_cases i <;> simp [s₁,words,state,nodesEmbedding,SpectralNodes.outputStore,SpectralNodes.inputStore]
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl)
  have h₂ : (copyOn (13:Fin 14) 1 9 (by decide) (by decide) (by decide)).Executes oracle s₁ s₂ (5*j+2) := by
    simpa [s₁,s₂,state] using copyOn_executes oracle (13:Fin 14) 1 9 (by decide) (by decide) (by decide) s₁ rfl
  obtain ⟨b,hb,hbb⟩ := SpectralNodeOmission.spectral_program_executes oracle g j hj
  have h₃ : eraseNode.Executes oracle s₂ s₃ b := by
    apply rename_executes_to SpectralNodeOmission.program omitEmbedding oracle hb
    · funext i;fin_cases i <;> simp [s₂,s₁,words,state,omitEmbedding,DH.Runtime.WordArray.store,DH.Runtime.WordArray.state]
    · funext i;fin_cases i <;> simp [s₃,others,value,state,omitEmbedding,DH.Runtime.WordArray.store,DH.Runtime.WordArray.state]
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 2 rfl)
  have h₄ : (clear (1:Fin 14)).Executes oracle s₃ (state g j (encodeBitList others) value) (j+1) := by
    convert clear_executes oracle (1:Fin 14) s₃ using 1
    · funext i;fin_cases i <;> simp [s₃,state]
    · simp [s₃]
  refine ⟨_,seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ (seq_executes _ _ oracle h₃ h₄)),?_⟩
  have hl := SpectralNodes.triangle_stream_length (g+1)
  rw [SpectralNodes.triangle_spectral] at hl
  have hjb : j≤(g+1)^2 := by
    have hc := spectralIndex_card_bound g
    rw [spectralIndices_length] at hj
    omega
  have hm := Nat.pow_le_pow_left (show
    (encodeBitList words).length+j+1≤(g+1)^2*(2*(4*(g+1)+2)+2)+(g+1)^2+1 by dsimp [words];nlinarith) 2
  simp only [time,streamBound,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_pow]
  dsimp [words] at hm
  nlinarith

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ SpectralNodes.program_queryFree)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
      (seq_queryFree _ _ (rename_queryFree _ _ SpectralNodeOmission.program_queryFree) (clear_queryFree _)))
end HiddenCircuits.Circuit.Runtime.SpectralFrontend
