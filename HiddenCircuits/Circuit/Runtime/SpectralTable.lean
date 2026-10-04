import HiddenCircuits.Circuit.Runtime.SpectralTableInit

/-! A fixed finite program generates the complete ordered spectral basis table. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTable
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

/-- Degree0 is preserved; count2 is unary; denominator3 and vector4 are canonical
self-delimiting streams in spectralIndices order. Every other tape is empty. -/
def publicStore (g : ℕ) (count outD outA : BitString) : Store 32 :=
  state g 0 count [] [] [] [] outD outA []

noncomputable def finish : OracleBlock 32 := seq (clear 1)
  (seq (reverseInPlace 3 5 6 (by decide) (by decide) (by decide))
    (reverseInPlace 4 5 6 (by decide) (by decide) (by decide)))
noncomputable def program : OracleBlock 32 := seq initializeTable (seq loop finish)
noncomputable def time : Polynomial ℕ := initTime+(X+1)^2*(bodyTime+3)+8*vectorBound+8*tableBound+26

theorem finish_executes (oracle : BitString → ℕ) (g n : ℕ) (count ds vs : BitString) :
    finish.Executes oracle (state g n count [] [] [] [] ds.reverse vs.reverse [])
      (publicStore g count ds vs) (n+8*ds.length+8*vs.length+21) := by
  let s₀ := state g n count [] [] [] [] ds.reverse vs.reverse []
  let s₁ := state g 0 count [] [] [] [] ds.reverse vs.reverse []
  let s₂ := state g 0 count [] [] [] [] ds vs.reverse []
  let s₃ := publicStore g count ds vs
  have h₁ : (clear (1:Fin 33)).Executes oracle s₀ s₁ (n+1) := by
    convert clear_executes oracle (1:Fin 33) s₀ using 1
    · funext i;fin_cases i <;> rfl
    · simp [s₀,state]
  have h₂ : (reverseInPlace (3:Fin 33) 5 6 (by decide) (by decide) (by decide)).Executes oracle s₁ s₂ (8*ds.length+8) := by
    convert reverseInPlace_executes oracle (3:Fin 33) 5 6 (by decide) (by decide) (by decide) s₁ rfl rfl using 1
    · funext i;fin_cases i <;> simp [s₁,s₂,state]
    · simp [s₁,state]
  have h₃ : (reverseInPlace (4:Fin 33) 5 6 (by decide) (by decide) (by decide)).Executes oracle s₂ s₃ (8*vs.length+8) := by
    convert reverseInPlace_executes oracle (4:Fin 33) 5 6 (by decide) (by decide) (by decide) s₂ rfl rfl using 1
    · funext i;fin_cases i <;> simp [s₂,s₃,publicStore,state]
    · simp [s₂,state]
  convert seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ h₃) using 1 <;> omega

/-- All basis entries are computed from the unary degree by bit-level programs;
no basis table or arithmetic certificate is supplied as input. -/
theorem program_executes (oracle : BitString → ℕ) (g : ℕ) :
    ∃ t, program.Executes oracle (publicStore g [] [] [])
      (publicStore g (List.replicate (nodeCount g) true)
        (encodeBitList (denominators g)) (encodeBitList (vectors g))) t ∧ t≤time.eval g := by
  obtain ⟨a,ha,hab⟩ := initializeTable_executes oracle g
  obtain ⟨b,hb,hbb⟩ := loop_executes oracle g (List.replicate (nodeCount g) true)
  have hc := finish_executes oracle g (nodeCount g) (List.replicate (nodeCount g) true)
    (encodeBitList (denominators g)) (encodeBitList (vectors g))
  refine ⟨a+(b+(nodeCount g+8*(encodeBitList (denominators g)).length+
    8*(encodeBitList (vectors g)).length+21)+2)+2,seq_executes _ _ oracle ha (seq_executes _ _ oracle hb hc),?_⟩
  have hn := nodeCount_bound g
  have hd := denominators_length g
  have hv := vectors_length g
  have hm := Nat.mul_le_mul_right (bodyTime.eval g+3) hn
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  change b≤nodeCount g*(bodyTime.eval g+2)+1 at hbb
  nlinarith

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ initializeTable_queryFree (seq_queryFree _ _ loop_queryFree
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _
      (reverseInPlace_queryFree _ _ _ _ _ _) (reverseInPlace_queryFree _ _ _ _ _ _))))

noncomputable def programOn {k : ℕ} (φ : Fin 33 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 33 ↪ Fin (k+1)) (oracle : BitString → ℕ)
    (s : Store k) (g : ℕ) (hs : s∘φ=publicStore g [] [] []) :
    ∃ t, (programOn φ).Executes oracle s
      (Function.update (Function.update (Function.update s (φ 2) (List.replicate (nodeCount g) true))
        (φ 3) (encodeBitList (denominators g))) (φ 4) (encodeBitList (vectors g))) t ∧ t≤time.eval g := by
  obtain ⟨t,ht,hb⟩ := program_executes oracle g
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ oracle ht hs
  · have he : (Function.update (Function.update (Function.update s (φ 2) (List.replicate (nodeCount g) true))
        (φ 3) (encodeBitList (denominators g))) (φ 4) (encodeBitList (vectors g)))∘φ=
      Function.update (Function.update (Function.update (s∘φ) 2 (List.replicate (nodeCount g) true))
        3 (encodeBitList (denominators g))) 4 (encodeBitList (vectors g)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj;rw [Function.update_of_ne (hj 4).symm,Function.update_of_ne (hj 3).symm,Function.update_of_ne (hj 2).symm]

theorem programOn_queryFree {k : ℕ} (φ : Fin 33 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralTable
