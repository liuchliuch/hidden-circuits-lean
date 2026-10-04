import HiddenCircuits.Circuit.Runtime.SpectralWeightsCorrectness

/-! Invoke the actual spectral-weight program at either
required fixed target, then physically erase its temporary mode bit. -/
namespace HiddenCircuits.Circuit.Runtime.SourceSpectralSetup
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

def outputStore (g : ℕ) (mode : Bool) : Store 35 := fun i =>
  if i.val=0 then List.replicate g true else if i.val=34 then signedBits (SpectralWeights.denominator g)
  else if i.val=35 then SpectralWeightsProgram.numeratorStream g mode else []
noncomputable def program (mode : Bool) : OracleBlock 35 :=
  seq (SpectralWeightsProgram.forMode mode) (clear 33)
noncomputable def time : Polynomial ℕ := SpectralWeightsProgram.unaryTime+4

theorem program_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    ∃c,(program mode).Executes oracle (Function.update (fun _ : Fin 36=>[]) 0 (List.replicate g true))
      (outputStore g mode) c ∧ c≤time.eval g := by
  obtain ⟨c,hc,hb⟩:=SpectralWeightsProgram.forMode_executes oracle g mode
  have he : (clear (33:Fin 36)).Executes oracle
      (SpectralWeightsProgram.publicStore g mode (signedBits (SpectralWeights.denominator g)) (SpectralWeightsProgram.numeratorStream g mode))
      (outputStore g mode) 2 := by
    convert clear_executes oracle (33:Fin 36)
      (SpectralWeightsProgram.publicStore g mode (signedBits (SpectralWeights.denominator g)) (SpectralWeightsProgram.numeratorStream g mode)) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨c+2+2,seq_executes _ _ oracle hc he,?_⟩
  simp only [time,eval_add,eval_ofNat]
  omega

lemma program_queryFree (mode : Bool) : (program mode).QueryFree :=
  seq_queryFree _ _ (SpectralWeightsProgram.forMode_queryFree mode) (clear_queryFree _)
noncomputable def on {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) (mode : Bool) : OracleBlock k := rename (program mode) φ

theorem on_executes {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) (oracle : BitString → ℕ) (s : Store k)
    (g : ℕ) (mode : Bool) (hs : s∘φ=Function.update (fun _ : Fin 36=>[]) 0 (List.replicate g true)) :
    ∃c,(on φ mode).Executes oracle s
      (Function.update (Function.update s (φ 34) (signedBits (SpectralWeights.denominator g)))
        (φ 35) (SpectralWeightsProgram.numeratorStream g mode)) c ∧ c≤time.eval g := by
  obtain ⟨c,hc,hb⟩:=program_executes oracle g mode
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ φ oracle hc hs
  · funext i
    have hi:=congrFun hs i
    change s (φ i)=_ at hi
    simp only [Function.comp_def,Function.update_apply,φ.injective.eq_iff,hi]
    fin_cases i <;> rfl
  · intro i hi;simp only [Function.update_of_ne (hi 34).symm,Function.update_of_ne (hi 35).symm]
lemma on_queryFree {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) (mode : Bool) : (on φ mode).QueryFree :=
  rename_queryFree _ _ (program_queryFree mode)
end HiddenCircuits.Circuit.Runtime.SourceSpectralSetup
