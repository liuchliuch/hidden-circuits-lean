import HiddenCircuits.Approximation.SelfReduction.Runtime.MapFrame

/-! A real loop body that parses one request, executes a supplied actual finite
program, and serializes its result. Callback time is fully charged. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def mapParseEmbedding (k : ℕ) : Fin 4 ↪ Fin (k+5) where
  toFun i := if i.val=0 then mapRight k 0 else if i.val=1 then 0 else if i.val=2 then mapRight k 2 else mapRight k 3
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [mapRight,Fin.ext_iff] <;> omega

noncomputable def mapParse (k : ℕ) : OracleBlock (k+4) := GraphVerifier.Runtime.unpairOn (mapParseEmbedding k)
noncomputable def mapCall {k : ℕ} (B : OracleBlock k) : OracleBlock (k+4) := rename B (mapLeft k)
noncomputable def mapBody {k : ℕ} (B : OracleBlock k) : OracleBlock (k+4) :=
  seq (mapParse k) (seq (clear (mapRight k 3)) (seq (mapCall B) (emitWordReversed 0 (mapRight k 1))))

 theorem mapParse_executes (k : ℕ) (g : BitString → ℕ) (word rest out : BitString) :
    (mapParse k).Executes g (mapStore k [] (pairBits word rest) out [] [])
      (mapStore k word rest out [] [true]) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes (mapParseEmbedding k) g
    (mapStore k [] (pairBits word rest) out [] []) (mapStore k word rest out [] [true]) (pairBits word rest)
    (by funext i; fin_cases i <;> simp [mapParseEmbedding] <;> rfl)
    (by funext i; fin_cases i <;> simp [mapParseEmbedding,GraphVerifier.parse_pair] <;> rfl)
    (by
      intro j
      refine Fin.addCases (m := k+1) (n := 4) (fun i => ?_) (fun i => ?_) j
      · intro hj
        by_cases hi : i=0
        · subst i; exact False.elim (hj 1 rfl)
        · simp [mapStore,mapLeft,hi]
      · intro hj
        fin_cases i
        · exact False.elim (hj 0 rfl)
        · simp [mapStore] <;> rfl
        · exact False.elim (hj 2 rfl)
        · exact False.elim (hj 3 rfl))
  convert h using 1
  simp [GraphVerifier.parse_pair, BinaryArithmetic.pair_parse_cost]
  omega

 theorem mapCall_executes {k : ℕ} (B : OracleBlock k) (g : BitString → ℕ)
    (word result rest out : BitString) (cost : ℕ)
    (h : B.Executes g (Function.update (fun _ => []) 0 word) (Function.update (fun _ => []) 0 result) cost) :
    (mapCall B).Executes g (mapStore k word rest out [] []) (mapStore k result rest out [] []) cost := by
  apply rename_executes_to B (mapLeft k) g h
  · funext i; simp [Function.comp_def,Function.update_apply]
  · funext i; simp [Function.comp_def,Function.update_apply]
  · intro j
    refine Fin.addCases (m := k+1) (n := 4) (fun i => ?_) (fun i => ?_) j
    · intro hj; exact False.elim (hj i rfl)
    · intro hj; simp [mapStore]

 theorem cleanCall_output_length {k : ℕ} (B : OracleBlock k) (g : BitString → ℕ)
    (word result : BitString) (cost : ℕ)
    (h : B.Executes g (Function.update (fun _ => []) 0 word) (Function.update (fun _ => []) 0 result) cost) :
    result.length ≤ word.length+cost := by
  have hs := h.stack_bound (n := word.length) (by
    intro i
    change (Function.update (fun _ : Fin (k+1) => ([] : BitString)) (0 : Fin (k+1)) word i).length ≤ word.length
    by_cases hi : i=(0 : Fin (k+1)) <;> simp [Function.update_apply,hi])
  simpa using hs (0 : Fin (k+1))

 theorem mapBody_executes {k : ℕ} (B : OracleBlock k) (g : BitString → ℕ)
    (word result rest out : BitString) (cost : ℕ)
    (h : B.Executes g (Function.update (fun _ => []) 0 word) (Function.update (fun _ => []) 0 result) cost) :
    ∃ t, (mapBody B).Executes g (mapStore k [] (pairBits word rest) out [] [])
      (mapStore k [] rest ((true::pairBits result []).reverse ++ out) [] []) t ∧
      t+2 ≤ 11*word.length+7*cost+20 := by
  have hp := mapParse_executes k g word rest out
  have hc : (clear (mapRight k 3)).Executes g (mapStore k word rest out [] [true]) (mapStore k word rest out [] []) 2 := by
    simpa using clear_executes g (mapRight k 3) (mapStore k word rest out [] [true])
  have hcall := mapCall_executes B g word result rest out cost h
  have he := emitWordReversed_executes g (0 : Fin (k+5)) (mapRight k 1)
    (by simpa only [mapLeft_zero] using mapLeft_ne_right k 0 1) (mapStore k result rest out [] [])
  have he' : (emitWordReversed (0 : Fin (k+5)) (mapRight k 1)).Executes g
      (mapStore k result rest out [] [])
      (mapStore k [] rest ((true::pairBits result []).reverse ++ out) [] []) (6*result.length+7) := by
    simpa using he
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hcall he')),?_⟩
  have hsize := cleanCall_output_length B g word result cost h
  omega

end HiddenCircuits.Approximation.SelfReduction.Runtime
