import HiddenCircuits.Approximation.Initialization.OuterLoop.Program

/-! The real bounded while program refines every branch of the
raw finite-tape extraction, including exhausted fuel and short tape padding. -/
namespace HiddenCircuits.Approximation.Initialization.OuterLoop
open Complexity Complexity.OracleBlock SamplerRuntime
set_option maxHeartbeats 2000000

lemma loop_execution (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (B fuel : ℕ)
    (U : Finset (Fin N)) (source : BitString) (π : Equiv.Perm (Fin N)) :
    ∃ (V : Finset (Fin N)) (ρ : Equiv.Perm (Fin N)) (tail : BitString) (t : ℕ),
      WhileExecution (51:Fin 52) body body g
        (state N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π)
          (RawExtraction.stageLength N B) fuel [])
        (state N G.bits (MaskEnumerationSemantics.mask V) tail B (Output.witness ρ)
          (RawExtraction.stageLength N B) 0 []) t ∧
      result V ρ=RawExtraction.run G B fuel U source π ∧ tail.length≤source.length ∧
      t≤loopBound (Search.Stage.timeBound N B (RawExtraction.stageLength N B)) fuel := by
  classical
  induction fuel generalizing U source π with
  | zero =>
    refine ⟨U,π,source,1,WhileExecution.empty _ rfl,?_,le_rfl,by simp [loopBound]⟩
    rfl
  | succ fuel ih =>
    let L := RawExtraction.stageLength N B
    let T := Search.Stage.timeBound N B L
    by_cases hU : U.Nonempty
    · cases hv : (List.finRange N).find? (CandidateTest.test G U B (TapeRead.takePadded L source) (U.min' hU)) with
      | none =>
        obtain ⟨a,ha,hab⟩ := Search.Stage.program_none g G U hU source B (Output.witness π) L hv
        have hs := stage_executes g N G.bits _ source B (Output.witness π) L fuel _ _ _ _ a ha
        have hb := seq_executes _ _ g hs (afterStage_false g N G.bits _ _ B (Output.witness π) L fuel)
        have hend := WhileExecution.empty (stack:=(51:Fin 52)) (B:=body) (C:=body) (g:=g)
          (state N G.bits (MaskEnumerationSemantics.mask U) (source.drop L) B (Output.witness π) L 0 []) rfl
        have hh := WhileExecution.one (show state N G.bits (MaskEnumerationSemantics.mask U) source B
          (Output.witness π) L (fuel+1) [] (51:Fin 52)=true::unary fuel by simp [state,List.replicate_succ]) (by rw [pop_fuel];exact hb) hend
        refine ⟨U,π,source.drop L,_,hh,?_,(by simp only [List.length_drop];omega),?_⟩
        · rw [result_nonempty U π hU]
          simp only [RawExtraction.run,dif_pos hU,hv,L]
        · unfold loopBound
          dsimp only [T,L] at *
          nlinarith
      | some v =>
        obtain ⟨V,ρ,tail,b,hb,hr,hlen,hbb⟩ := ih ((U.erase (U.min' hU)).erase v)
          (source.drop L) (MonotoneEndpoints.transpose π (U.min' hU) v)
        obtain ⟨a,ha,hab⟩ := Search.Stage.program_some g G U hU source B π L v hv
        have hs := stage_executes g N G.bits _ source B (Output.witness π) L fuel _ _ _ _ a ha
        have hbody := seq_executes _ _ g hs (afterStage_true g N G.bits _ _ B _ L fuel)
        have hh := WhileExecution.one (show state N G.bits (MaskEnumerationSemantics.mask U) source B
          (Output.witness π) L (fuel+1) [] (51:Fin 52)=true::unary fuel by simp [state,List.replicate_succ]) (by rw [pop_fuel];exact hbody) hb
        refine ⟨V,ρ,tail,_,hh,?_,hlen.trans ((by simp only [List.length_drop];omega)),?_⟩
        · simpa only [RawExtraction.run,dif_pos hU,hv,L] using hr
        · unfold loopBound at *
          dsimp only [T,L] at *
          nlinarith
    · have he : U=∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst U
      obtain ⟨V,ρ,tail,b,hb,hr,hlen,hbb⟩ := ih ∅ source π
      obtain ⟨a,ha,hab⟩ := Search.Stage.program_empty g G source B (Output.witness π) L
      have hs := stage_executes g N G.bits _ source B (Output.witness π) L fuel _ _ _ _ a ha
      have hbody := seq_executes _ _ g hs (afterStage_true g N G.bits _ _ B _ L fuel)
      have hh := WhileExecution.one (show state N G.bits (MaskEnumerationSemantics.mask ∅) source B
        (Output.witness π) L (fuel+1) [] (51:Fin 52)=true::unary fuel by simp [state,List.replicate_succ]) (by rw [pop_fuel];exact hbody) hb
      refine ⟨V,ρ,tail,_,hh,?_,hlen,?_⟩
      · simpa only [RawExtraction.run_empty] using hr
      · unfold loopBound at *
        dsimp only [T,L] at *
        nlinarith

/-- Concrete final residual set, permutation and tape tail, with the exact
RawExtraction.run result and the original polynomial loop bound. -/
theorem loop_executes (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (B fuel : ℕ)
    (U : Finset (Fin N)) (source : BitString) (π : Equiv.Perm (Fin N)) :
    ∃ (V : Finset (Fin N)) (ρ : Equiv.Perm (Fin N)) (tail : BitString) (t : ℕ),
      loop.Executes g
        (state N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π)
          (RawExtraction.stageLength N B) fuel [])
        (state N G.bits (MaskEnumerationSemantics.mask V) tail B (Output.witness ρ)
          (RawExtraction.stageLength N B) 0 []) t ∧
      result V ρ=RawExtraction.run G B fuel U source π ∧ tail.length≤source.length ∧
      t≤loopBound (Search.Stage.timeBound N B (RawExtraction.stageLength N B)) fuel := by
  obtain ⟨V,ρ,tail,t,ht,hr,hlen,hb⟩ := loop_execution g G B fuel U source π
  exact ⟨V,ρ,tail,t,whilePop_executes _ _ _ g ht,hr,hlen,hb⟩
end HiddenCircuits.Approximation.Initialization.OuterLoop
