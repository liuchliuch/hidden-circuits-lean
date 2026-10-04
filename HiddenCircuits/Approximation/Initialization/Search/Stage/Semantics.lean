import HiddenCircuits.Approximation.Initialization.Search.Stage.Decision

namespace HiddenCircuits.Approximation.Initialization.Search.Stage
open Complexity Complexity.OracleBlock SamplerRuntime

theorem after_pivot (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (hU : U.Nonempty) (source : BitString) (B : ℕ) (data : BitString) (L : ℕ)
    (target : Store 50) (t : ℕ)
    (ht : nonempty.Executes g
      (work N G.bits (MaskEnumerationSemantics.mask U) source B data L [] (U.min' hU).val [] [] [] [] []) target t) :
    ∃ c,program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) source B data L []) target c ∧
      c≤8*N+t+13 := by
  obtain ⟨a,ha,hab⟩ := pivot_executes g N G.bits (MaskEnumerationSemantics.mask U) source B data L
  have hp : SelfReduction.Runtime.seekPos (MaskEnumerationSemantics.mask U)=(U.min' hU).val :=
    SelfReduction.Runtime.seekPos_retainedMask_min U hU
  have hf : SelfReduction.Runtime.seekFound (MaskEnumerationSemantics.mask U)=true :=
    SelfReduction.Runtime.seekFound_retainedMask U hU
  rw [hp,hf] at ha
  have ht' : nonempty.Executes g
      (Function.update (work N G.bits (MaskEnumerationSemantics.mask U) source B data L [] (U.min' hU).val
        [true] [] [] [] []) (9:Fin 51) []) target t := by
    convert ht using 1
    funext r;fin_cases r <;> rfl
  have hb := branchPop_true (9:Fin 51) (finish true) (finish true) nonempty g rfl ht'
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  simp only [MaskEnumerationSemantics.mask,List.length_ofFn] at hab
  omega

theorem program_empty (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N)
    (source : BitString) (B : ℕ) (data : BitString) (L : ℕ) :
    ∃ t,program.Executes g (state N G.bits (MaskEnumerationSemantics.mask (∅:Finset (Fin N))) source B data L [])
      (state N G.bits (MaskEnumerationSemantics.mask (∅:Finset (Fin N))) source B data L [true]) t ∧
      t≤timeBound N B L := by
  let mask := MaskEnumerationSemantics.mask (∅:Finset (Fin N))
  obtain ⟨a,ha,hab⟩ := pivot_executes g N G.bits mask source B data L
  have hf : SelfReduction.Runtime.seekFound mask=false := by
    simp [mask,SelfReduction.Runtime.seekFound_eq_any,MaskEnumerationSemantics.mask]
  rw [hf] at ha
  have hc := finish_executes g N G.bits mask source B data L (SelfReduction.Runtime.seekPos mask) [] [] true
  have hc' : (finish true).Executes g
      (Function.update (work N G.bits mask source B data L [] (SelfReduction.Runtime.seekPos mask)
        [false] [] [] [] []) (9:Fin 51) [])
      (state N G.bits mask source B data L [true]) (SelfReduction.Runtime.seekPos mask+0+0+10) := by
    convert hc using 1
    funext r;fin_cases r <;> rfl
  have hb := branchPop_false (9:Fin 51) (finish true) (finish true) nonempty g rfl hc'
  refine ⟨_,seq_executes _ _ g ha hb,?_⟩
  have hp := SelfReduction.Runtime.seekPos_le_length mask
  have hl : mask.length=N := by simp [mask,MaskEnumerationSemantics.mask]
  rw [hl] at hab hp
  unfold timeBound
  omega

theorem program_none (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (hU : U.Nonempty) (source : BitString) (B : ℕ) (data : BitString) (L : ℕ)
    (hn : (List.finRange N).find? (CandidateTest.test G U B (TapeRead.takePadded L source) (U.min' hU))=none) :
    ∃ t,program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) source B data L [])
      (state N G.bits (MaskEnumerationSemantics.mask U) (source.drop L) B data L [false]) t ∧
      t≤timeBound N B L := by
  have hn' : Candidate.result G U B (TapeRead.takePadded L source) (U.min' hU)=none := by
    rw [Candidate.result_finRange,hn];rfl
  obtain ⟨a,ha,hab⟩ := choose_none g G U (source.drop L) B data L (U.min' hU) (TapeRead.takePadded L source) hn'
  have hp := prepare_executes g N G.bits (MaskEnumerationSemantics.mask U) source B data L (U.min' hU).val
  obtain ⟨t,ht,htb⟩ := after_pivot g G U hU source B data L _ _ (seq_executes _ _ g hp ha)
  refine ⟨t,ht,?_⟩
  simp only [TapeRead.prefix_length] at hab
  unfold timeBound
  omega

theorem program_some (g : BitString → ℕ) {N : ℕ} (G : MatrixGraph N) (U : Finset (Fin N))
    (hU : U.Nonempty) (source : BitString) (B : ℕ) (π : Equiv.Perm (Fin N)) (L : ℕ) (v : Fin N)
    (hv : (List.finRange N).find? (CandidateTest.test G U B (TapeRead.takePadded L source) (U.min' hU))=some v) :
    ∃ t,program.Executes g (state N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L [])
      (state N G.bits (MaskEnumerationSemantics.mask ((U.erase (U.min' hU)).erase v)) (source.drop L) B
        (Output.witness (MonotoneEndpoints.transpose π (U.min' hU) v)) L [true]) t ∧
      t≤timeBound N B L := by
  have hv' : Candidate.result G U B (TapeRead.takePadded L source) (U.min' hU)=some v.val := by
    rw [Candidate.result_finRange,hv];rfl
  obtain ⟨a,ha,hab⟩ := choose_some g G U (source.drop L) B π L (U.min' hU) v (TapeRead.takePadded L source) hv'
  have hp := prepare_executes g N G.bits (MaskEnumerationSemantics.mask U) source B (Output.witness π) L (U.min' hU).val
  obtain ⟨t,ht,htb⟩ := after_pivot g G U hU source B (Output.witness π) L _ _ (seq_executes _ _ g hp ha)
  refine ⟨t,ht,?_⟩
  simp only [TapeRead.prefix_length] at hab
  unfold timeBound
  omega

end HiddenCircuits.Approximation.Initialization.Search.Stage
