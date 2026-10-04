import HiddenCircuits.Circuit.Runtime.SpectralWeightsPrepare

/-! A single fixed bit-stack program, given only unary degree and a target bit,
computes the exact common-denominator interpolation weights in polynomial time. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralWeightsProgram
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial
open SpectralWeights

def zerosEmbedding : Fin 2 ↪ Fin 36 := pairEmbedding 2 7 (by decide)
 def foldEmbedding : Fin 25 ↪ Fin 36 where
  toFun i := if i.val=0 then 8 else if i.val=1 then 9 else if i.val=2 then 7 else
    if i.val=21 then 4 else if i.val=22 then 6 else if i.val=23 then 28 else if i.val=24 then 29 else ⟨i.val+7,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def zeros : OracleBlock 35 := rename SpectralZeroVector.program zerosEmbedding
noncomputable def fold : OracleBlock 35 := rename SpectralFold.loop foldEmbedding
noncomputable def finish : OracleBlock 35 := seq (moveOn 5 34 8 (by decide) (by decide) (by decide))
  (moveOn 7 35 8 (by decide) (by decide) (by decide))
noncomputable def program : OracleBlock 35 := seq prepare (seq zeros (seq fold finish))
noncomputable def time : Polynomial ℕ := prepareTime+SpectralFold.time+15*(X+1)^2+
  6*SpectralFold.scalarBound+6*SpectralFold.vectorStreamBound+30

/-- Input degree on0, mode bit on33 (false=0, true=−1); output common signed
denominator on34 and canonical signed numerator-vector stream on35. -/
def publicStore (g : ℕ) (mode : Bool) (outD outN : BitString) : Store 35 :=
  state g mode [] [] [] [] [] [] outD outN

 theorem zeros_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    zeros.Executes oracle
      (state g mode (countWord g) [] (tableStream g) (signedBits (denominator g)) (scaleStream g mode) [] [] [])
      (state g mode [] [] (tableStream g) (signedBits (denominator g)) (scaleStream g mode)
        (encodeBitList ((List.replicate (Fintype.card (SpectralIndex g)) (0:ℤ)).map signedBits)) [] [])
      (15*Fintype.card (SpectralIndex g)+1) := by
  have ht := SpectralZeroVector.program_executes oracle (Fintype.card (SpectralIndex g))
  apply rename_executes_to SpectralZeroVector.program zerosEmbedding oracle ht
  · funext i;fin_cases i
    · simp [Function.comp_def,state,zerosEmbedding,pairEmbedding,SpectralZeroVector.state,countWord,SpectralTable.nodeCount,spectralIndices_length]
    · rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)

 theorem fold_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    ∃ t, fold.Executes oracle
      (state g mode [] [] (tableStream g) (signedBits (denominator g)) (scaleStream g mode)
        (encodeBitList ((List.replicate (Fintype.card (SpectralIndex g)) (0:ℤ)).map signedBits)) [] [])
      (state g mode [] [] [] (signedBits (denominator g)) [] (numeratorStream g mode) [] []) t ∧
      t≤SpectralFold.time.eval g := by
  obtain ⟨t,ht,hb⟩ := SpectralFold.loop_executes oracle g (SpectralTargets.base mode) (base_abs mode)
  refine ⟨t,?_,hb⟩
  apply rename_executes_to SpectralFold.loop foldEmbedding oracle ht
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 2 rfl) | exact False.elim (hi 21 rfl) | exact False.elim (hi 22 rfl)

 theorem finish_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    finish.Executes oracle
      (state g mode [] [] [] (signedBits (denominator g)) [] (numeratorStream g mode) [] [])
      (publicStore g mode (signedBits (denominator g)) (numeratorStream g mode))
      (6*(signedBits (denominator g)).length+6*(numeratorStream g mode).length+12) := by
  let s₀ := state g mode [] [] [] (signedBits (denominator g)) [] (numeratorStream g mode) [] []
  let s₁ := state g mode [] [] [] [] [] (numeratorStream g mode) (signedBits (denominator g)) []
  let s₂ := publicStore g mode (signedBits (denominator g)) (numeratorStream g mode)
  have h₁ : (moveOn (5:Fin 36) 34 8 (by decide) (by decide) (by decide)).Executes oracle s₀ s₁
      (6*(signedBits (denominator g)).length+5) := by
    convert moveOn_executes oracle (5:Fin 36) 34 8 (by decide) (by decide) (by decide) s₀ rfl using 1
    funext i;fin_cases i <;> simp [s₀,s₁,state]
  have h₂ : (moveOn (7:Fin 36) 35 8 (by decide) (by decide) (by decide)).Executes oracle s₁ s₂
      (6*(numeratorStream g mode).length+5) := by
    convert moveOn_executes oracle (7:Fin 36) 35 8 (by decide) (by decide) (by decide) s₁ rfl using 1
    funext i;fin_cases i <;> simp [s₁,s₂,state,publicStore]
  convert seq_executes _ _ oracle h₁ h₂ using 1 <;> omega

 theorem program_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    ∃ t, program.Executes oracle (publicStore g mode [] [])
      (publicStore g mode (signedBits (denominator g)) (numeratorStream g mode)) t ∧ t≤time.eval g := by
  obtain ⟨a,ha,hab⟩ := prepare_executes oracle g mode
  have hb := zeros_executes oracle g mode
  obtain ⟨c,hc,hcb⟩ := fold_executes oracle g mode
  have hd := finish_executes oracle g mode
  refine ⟨a+((15*Fintype.card (SpectralIndex g)+1)+(c+(6*(signedBits (denominator g)).length+
    6*(numeratorStream g mode).length+12)+2)+2)+2,
    seq_executes _ _ oracle ha (seq_executes _ _ oracle hb (seq_executes _ _ oracle hc hd)),?_⟩
  have hn := spectralIndex_card_bound g
  have hD := denominator_length g
  have hV := SpectralFold.vector_length_bound g (SpectralTargets.base mode) (base_abs mode) (spectralIndices g)
    (by rw [spectralIndices_length];exact hn)
  change (numeratorStream g mode).length≤SpectralFold.vectorStreamBound.eval g at hV
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  omega

 theorem numeratorStream_eq (g : ℕ) (mode : Bool) : numeratorStream g mode=
    encodeBitList ((List.ofFn (fun k : Fin (Fintype.card (SpectralIndex g)) =>
      (spectralWeightData g (SpectralTargets.base mode) k.val).1)).map signedBits) := by
  unfold numeratorStream
  rw [vector_complete]

/-- The output bytes are exactly the mathematically proved spectralWeightData,
including a nonzero common denominator, not merely an equivalent certificate. -/
 theorem program_weightData_executes (oracle : BitString → ℕ) (g : ℕ) (mode : Bool) :
    ∃ t, program.Executes oracle (publicStore g mode [] [])
      (publicStore g mode (signedBits (spectralWeightData g (SpectralTargets.base mode) 0).2)
        (encodeBitList ((List.ofFn (fun k : Fin (Fintype.card (SpectralIndex g)) =>
          (spectralWeightData g (SpectralTargets.base mode) k.val).1)).map signedBits))) t ∧ t≤time.eval g := by
  simpa only [denominator_data g (SpectralTargets.base mode) 0,numeratorStream_eq] using program_executes oracle g mode

 theorem program_queryFree : program.QueryFree := seq_queryFree _ _ prepare_queryFree
  (seq_queryFree _ _ (rename_queryFree _ _ SpectralZeroVector.program_queryFree)
    (seq_queryFree _ _ (rename_queryFree _ _ SpectralFold.loop_queryFree)
      (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (moveOn_queryFree _ _ _ _ _ _))))

noncomputable def programOn {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : OracleBlock k := rename program φ

 theorem programOn_executes {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) (oracle : BitString → ℕ)
    (s : Store k) (g : ℕ) (mode : Bool) (hs : s∘φ=publicStore g mode [] []) :
    ∃ t, (programOn φ).Executes oracle s
      (Function.update (Function.update s (φ 34) (signedBits (denominator g))) (φ 35) (numeratorStream g mode)) t ∧
      t≤time.eval g := by
  obtain ⟨t,ht,hb⟩ := program_executes oracle g mode
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ oracle ht hs
  · have he : (Function.update (Function.update s (φ 34) (signedBits (denominator g)))
        (φ 35) (numeratorStream g mode))∘φ=Function.update (Function.update (s∘φ) 34
          (signedBits (denominator g))) 35 (numeratorStream g mode) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro j hj;rw [Function.update_of_ne (hj 35).symm,Function.update_of_ne (hj 34).symm]

 theorem programOn_queryFree {k : ℕ} (φ : Fin 36 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree
end HiddenCircuits.Circuit.Runtime.SpectralWeightsProgram
