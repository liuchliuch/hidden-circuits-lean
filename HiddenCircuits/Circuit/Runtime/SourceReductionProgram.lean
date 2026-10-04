import HiddenCircuits.Circuit.Runtime.SourceReductionFrame

/-! The actual graph-to-WordEval source reduction, including its raw input
frontend, nested interpolation, exact output division, and full-bank cleanup. -/
namespace HiddenCircuits.Circuit.Runtime.SourceReduction
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial SourceFrontend

noncomputable def positive {k : ℕ} (W : OracleBlock k) : OracleBlock (k+69) :=
  seq (front k) (seq (SourceOuter.program W) (SourceFinalization.program k))
noncomputable def select {k : ℕ} (W : OracleBlock k) : OracleBlock (k+69) :=
  branchPop (lowPort k 23) (lift k (SourceZero.on 0)) (positive W) (positive W)
noncomputable def program {k : ℕ} (W : OracleBlock k) : OracleBlock (k+69) :=
  seq (lift k metadata) (select W)
noncomputable def inputBound : Polynomial ℕ := X+SourceMetadata.time
noncomputable def prefixTime (p : Polynomial ℕ) : Polynomial ℕ := frontTime.comp inputBound+SourceOuter.sourceTime p+2
noncomputable def positiveTime (k : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  prefixTime p+(SourceFinalization.time k).comp (inputBound+prefixTime p)+2
noncomputable def time (k : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  SourceMetadata.time+positiveTime k p+11

theorem positive_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (G : MatrixGraph n)
    (wire : BitString)
    (hsize : ∀i,(rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) wire i).length ≤
      inputBound.eval (GraphInput.encode ⟨n,G⟩).length) :
    ∃t, (positive W).Executes g
      (frame k (rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) wire) [] [])
      (Function.update (fun _ : Fin (k+70)=>([]:BitString)) 0 (Computability.encodeNat G.independentCount)) t ∧
      t ≤ (positiveTime k p).eval (GraphInput.encode ⟨n,G⟩).length := by
  let L := (GraphInput.encode ⟨n,G⟩).length
  let B := inputBound.eval L
  obtain ⟨a,ha,hab⟩ := front_executes k g (restoringIndependentProgram G).gates
    (2*restoringSwapPairs (sourceEdges G)) wire B hsize
  obtain ⟨b,hb,hbb⟩ := SourceOuter.source_executes W g p hW hn G
  have habExec := seq_executes _ _ g ha hb
  have hbound := habExec.stack_bound (frame_bound k _ B hsize)
  have hcorrect := SourceOuter.sourceResult_correct hn G
  obtain ⟨c,hc,hcb⟩ := SourceFinalization.executes k g _ (SourceOuter.sourceResult hn G) G.independentCount
    (B+(a+b+2)) (final_projection k _ _ _) hbound hcorrect.1 hcorrect.2
  have hprefix : a+b+2 ≤ (prefixTime p).eval L := by
    simp only [prefixTime,eval_add,eval_comp,eval_ofNat]
    exact Nat.add_le_add_right (Nat.add_le_add hab hbb) 2
  have hmono := polynomial_nat_eval_mono (SourceFinalization.time k) (Nat.add_le_add_left hprefix B)
  dsimp only at hmono
  refine ⟨a+(b+c+2)+2,seq_executes _ _ g ha (seq_executes _ _ g hb hc),?_⟩
  change a+(b+c+2)+2 ≤ (positiveTime k p).eval L
  simp only [positiveTime,eval_add,eval_comp,eval_ofNat]
  dsimp only [B] at hcb hmono
  omega

lemma raw_zero (G : MatrixGraph 0) :
    rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) []=
      Function.update (fun _ : Fin 64=>([]:BitString)) 0 [false] := by
  have he : sourceEdges G=[] := by simp [sourceEdges,show orderedEdges G=[] from rfl]
  have hw := SourceZero.gates_nil (restoringIndependentProgram G).gates
  rw [he]
  funext i;fin_cases i <;> simp [rawStore,hw,restoringSwapPairs,circuitBits,forbidOccurrences,signOccurrences] <;> rfl

theorem program_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) (G : GraphInput) :
    ∃t, (program W).Executes g
      (Function.update (fun _ : Fin (k+70)=>([]:BitString)) 0 (GraphInput.encode G))
      (Function.update (fun _ : Fin (k+70)=>([]:BitString)) 0 (Computability.encodeNat G.2.independentCount)) t ∧
      t ≤ (time k p).eval (GraphInput.encode G).length := by
  obtain ⟨n,G⟩ := G
  obtain ⟨a,ha,hab⟩ := metadata_executes g G
  have hwide := lift_executes k metadata g _ _ [] [] a ha
  rw [frame_initial] at hwide
  have hi : ∀i : Fin 64,(Function.update (fun _ : Fin 64=>([]:BitString)) 0 (GraphInput.encode ⟨n,G⟩) i).length ≤
      (GraphInput.encode ⟨n,G⟩).length := by
    intro i
    simp only [Function.update_apply]
    split_ifs <;> simp only [List.length_nil,Nat.zero_le,le_refl]
  have hsize := ha.stack_bound hi
  have hbound : ∀i,(rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) (List.replicate n true) i).length ≤
      inputBound.eval (GraphInput.encode ⟨n,G⟩).length := by
    intro i
    have h := hsize i
    change (rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) (List.replicate n true) i).length ≤
      (GraphInput.encode ⟨n,G⟩).length+a at h
    simp only [inputBound,eval_add,eval_X]
    omega
  by_cases hn:n=0
  · subst n
    have hz := SourceZero.on_executes (0:Fin 64) g (Function.update (fun _ : Fin 64=>([]:BitString)) 0 [false]) (by simp)
    simp only [Function.update_idem] at hz
    have hzWide := lift_executes k (SourceZero.on 0) g _ _ [] [] 5 hz
    rw [frame_initial,frame_initial] at hzWide
    have hin : frame k (rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) (List.replicate 0 true)) [] []=
        Function.update (fun _ : Fin (k+70)=>([]:BitString)) 0 [false] := by
      rw [List.replicate_zero,raw_zero,frame_initial]
    rw [hin] at hwide
    have hs : (Function.update (fun _ : Fin (k+70)=>([]:BitString)) 0 [false]) (lowPort k 23)=[] := by simp [lowPort,Fin.ext_iff,FramedFor.embedding,SourceWordCall.lowEmbedding]
    have hbranch := branchPop_empty (lowPort k 23) (lift k (SourceZero.on 0)) (positive W) (positive W) g hs hzWide
    refine ⟨a+7+2,?_,?_⟩
    · simpa only [SourceZero.independentCount_zero G] using seq_executes _ _ g hwide hbranch
    · simp only [time,eval_add,eval_ofNat]
      omega
  · have hp : 0<n := by omega
    let tail := List.replicate (n-1) true
    obtain ⟨b,hb,hbb⟩ := positive_executes W g p hW hp G tail
      (rawStore_wire_bound _ _ _ (List.replicate n true) tail hbound (by simp [tail]))
    have hs : frame k (rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) (List.replicate n true)) [] [] (lowPort k 23)=true::tail := by
      rw [frame_low]
      change List.replicate n true=true::List.replicate (n-1) true
      have he : n=(n-1)+1 := by omega
      conv_lhs => rw [he]
      rw [List.replicate_succ]
    have hb' : (positive W).Executes g
        (Function.update (frame k (rawStore (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) (List.replicate n true)) [] []) (lowPort k 23) tail)
        (Function.update (fun _ : Fin (k+70)=>([]:BitString)) 0 (Computability.encodeNat G.independentCount)) b := by
      rwa [frame_update_low,rawStore_update_wire]
    have hbranch := branchPop_true (lowPort k 23) (lift k (SourceZero.on 0)) (positive W) (positive W) g hs hb'
    refine ⟨a+(b+2)+2,seq_executes _ _ g hwide hbranch,?_⟩
    simp only [time,eval_add,eval_ofNat]
    omega
end HiddenCircuits.Circuit.Runtime.SourceReduction
