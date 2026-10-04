import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.Circuit.Runtime.SpectralCoefficientsNodes

/-! Complete binary program for the integer coefficient array ∏(X−node). -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic Polynomial

noncomputable def initializeNodes : OracleBlock 22 :=
  seq (moveOn 0 20 2 (by decide) (by decide) (by decide))
    (prepend 1 (encodeBitList [signedBits 1]))
noncomputable def program : OracleBlock 22 :=
  seq initializeNodes (seq nodeLoop (moveOn 1 0 2 (by decide) (by decide) (by decide)))
noncomputable def time : Polynomial ℕ := X*(nodeBodyTime+2)+6*X+6*coefficientStreamBound+36

theorem initializeNodes_executes (g : BitString → ℕ) (input : BitString) :
    initializeNodes.Executes g (Function.update (fun _ : Fin 23 => ([]:BitString)) 0 input)
      (nodeStore [] (encodeBitList [signedBits 1]) input []) (6*input.length+26) := by
  let s₀ : Store 22 := Function.update (fun _ => []) 0 input
  let s₁ := nodeStore [] [] input []
  have h₁ : (moveOn (0:Fin 23) 20 2 (by decide) (by decide) (by decide)).Executes g s₀ s₁ (6*input.length+5) := by
    convert moveOn_executes g (0:Fin 23) 20 2 (by decide) (by decide) (by decide) s₀ rfl using 1
    funext i;fin_cases i <;> simp [s₀,s₁,nodeStore]
  have h₂ : (prepend (1:Fin 23) (encodeBitList [signedBits 1])).Executes g s₁
      (nodeStore [] (encodeBitList [signedBits 1]) input []) 19 := by
    convert prepend_executes g (1:Fin 23) (encodeBitList [signedBits 1]) s₁ using 1
    funext i;fin_cases i <;> simp [s₁,nodeStore]
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

/-- Every root and every coefficient is physically read, multiplied, added and
serialized. The bound depends only on the actual signed input stream length. -/
theorem program_executes (g : BitString → ℕ) (xs : List ℤ) :
    ∃ t, program.Executes g
      (Function.update (fun _ : Fin 23 => ([]:BitString)) 0 (encodeBitList (xs.map signedBits)))
      (Function.update (fun _ : Fin 23 => ([]:BitString)) 0 (encodeBitList ((coefficients xs).map signedBits))) t ∧
      t≤time.eval (encodeBitList (xs.map signedBits)).length := by
  let N := (encodeBitList (xs.map signedBits)).length
  have hlen : xs.length≤N := by
    simpa only [List.length_map] using list_length_le_encodeBitList_length (xs.map signedBits)
  have hxs : ∀z∈xs,(signedBits z).length≤N := by
    intro z hz
    exact member_length_le_encodeBitList (List.mem_map.mpr ⟨z,hz,rfl⟩)
  have hi := initializeNodes_executes g (encodeBitList (xs.map signedBits))
  obtain ⟨c,hc,hcb⟩ := nodeLoop_executes g xs [] N (by simpa using hlen) hxs (by simp)
  have hz : coefficients []=[1] := rfl
  simp only [hz,List.map_cons,List.map_nil,List.append_nil,coefficients_reverse] at hc
  let out := encodeBitList ((coefficients xs).map signedBits)
  have hf : (moveOn (1:Fin 23) 0 2 (by decide) (by decide) (by decide)).Executes g
      (nodeStore [] out [] []) (Function.update (fun _ : Fin 23 => ([]:BitString)) 0 out) (6*out.length+5) := by
    convert moveOn_executes g (1:Fin 23) 0 2 (by decide) (by decide) (by decide) (nodeStore [] out [] []) rfl using 1
    funext i;fin_cases i <;> simp [nodeStore]
  refine ⟨(6*N+26)+(c+(6*out.length+5)+2)+2,seq_executes _ _ g hi (seq_executes _ _ g hc hf),?_⟩
  have ho := coefficientStream_length xs N hlen hxs
  have hm := Nat.mul_le_mul_right (nodeBodyTime.eval N+2) hlen
  simp only [time,eval_add,eval_mul,eval_X,eval_ofNat]
  change (6*N+26)+(c+(6*out.length+5)+2)+2≤N*(nodeBodyTime.eval N+2)+6*N+6*coefficientStreamBound.eval N+36
  dsimp [out]
  omega

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (prepend_queryFree _ _))
    (seq_queryFree _ _ nodeLoop_queryFree (moveOn_queryFree _ _ _ _ _ _))

theorem program_runs (g : BitString → ℕ) (xs : List ℤ) :
    ∃ c t, program.machine.Runs g (program.machine.init (encodeBitList (xs.map signedBits))) c t ∧
      c.stack=Function.update (fun _ : Fin 23 => ([]:BitString)) 0 (encodeBitList ((coefficients xs).map signedBits)) ∧
      t≤time.eval (encodeBitList (xs.map signedBits)).length := by
  obtain ⟨t,ht,hb⟩ := program_executes g xs
  refine ⟨program.config program.exit _,t,?_,rfl,hb⟩
  apply (OracleMachine.runs_iff_steps_halt _).mpr
  exact ⟨ht,by simp [OracleMachine.step,machine,config,program.exit_halt]⟩

noncomputable def programOn {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem programOn_executes {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) (g : BitString → ℕ) (s : Store k)
    (xs : List ℤ) (hs : s∘φ=Function.update (fun _ : Fin 23 => ([]:BitString)) 0 (encodeBitList (xs.map signedBits))) :
    ∃ t, (programOn φ).Executes g s
      (Function.update s (φ 0) (encodeBitList ((coefficients xs).map signedBits))) t ∧
      t≤time.eval (encodeBitList (xs.map signedBits)).length := by
  obtain ⟨t,ht,hb⟩ := program_executes g xs
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 0) (encodeBitList ((coefficients xs).map signedBits)))∘φ=
        Function.update (s∘φ) 0 (encodeBitList ((coefficients xs).map signedBits)) := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    simp only [he,hs,Function.update_idem]
  · intro j hj;exact Function.update_of_ne (hj 0).symm _ _

theorem programOn_queryFree {k : ℕ} (φ : Fin 23 ↪ Fin (k+1)) : (programOn φ).QueryFree :=
  rename_queryFree _ _ program_queryFree

/-- The actual emitted coefficient at every index is the actual integer
polynomial-product coefficient, including zeros outside its support. -/
theorem emitted_coefficient (xs : List ℤ) (k : ℕ) :
    (coefficients xs)[k]?.getD 0=(IntegerSpectralWeights.poly xs).coeff k := by
  rw [coefficients_get,IntegerSpectralWeights.coeffs_eq]
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
