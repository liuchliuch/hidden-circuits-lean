import HiddenCircuits.Circuit.Runtime.SpectralTableData

/-! One actual indexed basis-table row, including both independent output streams. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralTable
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

def state (g j : ℕ) (count roots value nums den outD outA clock : BitString) : Store 32 := fun i =>
  if i.val=0 then List.replicate g true else if i.val=1 then List.replicate j true else if i.val=2 then count
  else if i.val=3 then outD else if i.val=4 then outA else if i.val=5 then roots else if i.val=6 then value
  else if i.val=30 then nums else if i.val=31 then den else if i.val=32 then clock else []

def frontendEmbedding : Fin 14 ↪ Fin 33 where
  toFun i := if i.val=0 then 5 else if i.val=2 then 6 else if i.val=12 then 0 else if i.val=13 then 1 else ⟨i.val+6,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
 def basisEmbedding : Fin 27 ↪ Fin 33 where
  toFun i := if i.val=0 then 6 else if i.val=1 then 5 else if i.val=2 then 30 else if i.val=3 then 31 else ⟨i.val+3,by omega⟩
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def frontend : OracleBlock 32 := rename SpectralFrontend.program frontendEmbedding
noncomputable def basis : OracleBlock 32 := SpectralBasis.programOn basisEmbedding
noncomputable def body : OracleBlock 32 := seq frontend (seq basis
  (seq (emitOn 30 4 (by decide)) (seq (emitOn 31 3 (by decide))
    (seq (clear 5) (seq (clear 6) (push 1 true))))))

theorem frontend_executes (oracle : BitString → ℕ) (g j : ℕ) (hj : j<(spectralIndices g).length)
    (count outD outA clock : BitString) :
    ∃ t, frontend.Executes oracle (state g j count [] [] [] [] outD outA clock)
      (state g j count (rootWord g j) (valueWord g j) [] [] outD outA clock) t ∧ t≤SpectralFrontend.time.eval g := by
  obtain ⟨t,ht,hb⟩ := SpectralFrontend.program_executes oracle g j hj
  refine ⟨t,?_,hb⟩
  apply rename_executes_to SpectralFrontend.program frontendEmbedding oracle ht
  · funext i;fin_cases i <;> simp [Function.comp_def,state,frontendEmbedding,SpectralFrontend.state]
  · funext i;fin_cases i <;> simp [Function.comp_def,state,frontendEmbedding,SpectralFrontend.state,
      rootWord,valueWord,indexAt,hj,SpectralBasis.roots]
  · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 2 rfl)

theorem basis_executes (oracle : BitString → ℕ) (g j : ℕ) (count outD outA clock : BitString) :
    ∃ t, basis.Executes oracle (state g j count (rootWord g j) (valueWord g j) [] [] outD outA clock)
      (state g j count (rootWord g j) (valueWord g j) (coefficientWord g j) (denominatorWord g j) outD outA clock) t ∧
      t≤SpectralBasis.spectralTime.eval g := by
  let s := state g j count (rootWord g j) (valueWord g j) [] [] outD outA clock
  obtain ⟨t,ht,hb⟩ := SpectralBasis.programOn_executes basisEmbedding oracle s
    (spectralIntegerNode (indexAt g j)) (SpectralBasis.roots g (indexAt g j))
    (by funext i;fin_cases i <;> rfl)
  refine ⟨t,?_,hb.trans ?_⟩
  · convert ht using 1
    funext i;fin_cases i <;> simp [s,state,basisEmbedding,coefficientWord,denominatorWord,
      SpectralBasis.coefficientVector,spectralBasisDenominator,LagrangeIntegerArrays.basisDenominator,SpectralBasis.roots]
  · have hm := polynomial_nat_eval_mono SpectralBasis.time (SpectralBasis.spectral_input_length g (indexAt g j))
    simpa only [SpectralBasis.spectralTime,eval_comp] using hm

theorem body_executes (oracle : BitString → ℕ) (g j : ℕ) (hj : j<(spectralIndices g).length)
    (count outD outA clock : BitString) :
    ∃ t, body.Executes oracle (state g j count [] [] [] [] outD outA clock)
      (state g (j+1) count [] [] [] []
        ((wordChunk (denominatorWord g j)).reverse++outD) ((wordChunk (coefficientWord g j)).reverse++outA) clock) t ∧
      t≤bodyTime.eval g := by
  let ds := (wordChunk (denominatorWord g j)).reverse++outD
  let vs := (wordChunk (coefficientWord g j)).reverse++outA
  let s₀ := state g j count [] [] [] [] outD outA clock
  let s₁ := state g j count (rootWord g j) (valueWord g j) [] [] outD outA clock
  let s₂ := state g j count (rootWord g j) (valueWord g j) (coefficientWord g j) (denominatorWord g j) outD outA clock
  let s₃ := state g j count (rootWord g j) (valueWord g j) [] (denominatorWord g j) outD vs clock
  let s₄ := state g j count (rootWord g j) (valueWord g j) [] [] ds vs clock
  let s₅ := state g j count [] (valueWord g j) [] [] ds vs clock
  let s₆ := state g j count [] [] [] [] ds vs clock
  let s₇ := state g (j+1) count [] [] [] [] ds vs clock
  obtain ⟨a,ha,hab⟩ := frontend_executes oracle g j hj count outD outA clock
  obtain ⟨b,hb,hbb⟩ := basis_executes oracle g j count outD outA clock
  have h₃ : (emitOn (30:Fin 33) 4 (by decide)).Executes oracle s₂ s₃ (6*(coefficientWord g j).length+7) := by
    convert emitOn_executes oracle (30:Fin 33) 4 (by decide) s₂ using 1
    funext i;fin_cases i <;> simp [s₂,s₃,state,vs]
  have h₄ : (emitOn (31:Fin 33) 3 (by decide)).Executes oracle s₃ s₄ (6*(denominatorWord g j).length+7) := by
    convert emitOn_executes oracle (31:Fin 33) 3 (by decide) s₃ using 1
    funext i;fin_cases i <;> simp [s₃,s₄,state,ds]
  have h₅ : (clear (5:Fin 33)).Executes oracle s₄ s₅ ((rootWord g j).length+1) := by
    convert clear_executes oracle (5:Fin 33) s₄ using 1
    funext i;fin_cases i <;> rfl
  have h₆ : (clear (6:Fin 33)).Executes oracle s₅ s₆ ((valueWord g j).length+1) := by
    convert clear_executes oracle (6:Fin 33) s₅ using 1
    funext i;fin_cases i <;> rfl
  have h₇ : (push (1:Fin 33) true).Executes oracle s₆ s₇ 1 := by
    convert push_executes oracle (1:Fin 33) true s₆ using 1
    funext i;fin_cases i <;> simp [s₆,s₇,state,List.replicate_succ]
  refine ⟨a+(b+((6*(coefficientWord g j).length+7)+((6*(denominatorWord g j).length+7)+
    (((rootWord g j).length+1)+(((valueWord g j).length+1)+1+2)+2)+2)+2)+2)+2,
    seq_executes _ _ oracle ha (seq_executes _ _ oracle hb (seq_executes _ _ oracle h₃
      (seq_executes _ _ oracle h₄ (seq_executes _ _ oracle h₅ (seq_executes _ _ oracle h₆ h₇))))),?_⟩
  have hd := denominatorWord_length g j
  have hv := coefficientWord_length g j
  have hr := root_value_length g j
  simp only [bodyTime,eval_add,eval_mul,eval_ofNat]
  omega

theorem body_queryFree : body.QueryFree :=
  seq_queryFree _ _ (rename_queryFree _ _ SpectralFrontend.program_queryFree)
    (seq_queryFree _ _ (SpectralBasis.programOn_queryFree _)
      (seq_queryFree _ _ (emitOn_queryFree _ _ _) (seq_queryFree _ _ (emitOn_queryFree _ _ _)
        (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))))))
end HiddenCircuits.Circuit.Runtime.SpectralTable
