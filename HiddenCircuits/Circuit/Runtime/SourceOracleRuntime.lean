import HiddenCircuits.Circuit.Runtime.SourceLoopSemantics

/-! The concrete source driver has polynomial charged time
in the original graph input bytes, with its full-grid accumulator bound discharged. -/
namespace HiddenCircuits.Circuit.Runtime.SourceOuter
open HiddenCircuits.Complexity OracleBlock BinaryArithmetic Polynomial

noncomputable def sourceInputSize : Polynomial ℕ := SourceQueryBounds.sourceInputSize
noncomputable def sourceRegisterSize : Polynomial ℕ := sourceInputSize+SourceQueryEnumeration.prefixBitSize.comp sourceInputSize
noncomputable def sourceTime (p : Polynomial ℕ) : Polynomial ℕ := (time p).comp sourceRegisterSize
noncomputable def sourceResult {n : ℕ} (hn : 0<n) (G : MatrixGraph n) : RationalAccumulator.Ratio :=
  result hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates (0,1)

lemma source_input_bound {n : ℕ} (G : MatrixGraph n) :
    (circuitBits n (restoringIndependentProgram G).gates).length+2*restoringSwapPairs (sourceEdges G)≤
      sourceInputSize.eval (GraphInput.encode ⟨n,G⟩).length := SourceQueryBounds.source_input_bound G

theorem source_executes {k : ℕ} (W : OracleBlock k) (g : BitString → ℕ) (p : Polynomial ℕ)
    (hW : SourceWordCall.WordSolverSpec W g p) {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    ∃c,(program W).Executes g
      (state (k:=k) (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) 0 (0,1))
      (state (k:=k) (restoringIndependentProgram G).gates (2*restoringSwapPairs (sourceEdges G)) 0 (sourceResult hn G)) c ∧
      c≤(sourceTime p).eval (GraphInput.encode ⟨n,G⟩).length := by
  let C:=(SourceQueryEnumeration.prefixBitSize.comp sourceInputSize).eval (GraphInput.encode ⟨n,G⟩).length
  have hbit:=SourceQueryEnumeration.source_bitBound hn G
  obtain ⟨c,hc,hb,_⟩:=program_executes W g p hW hn (2*restoringSwapPairs (sourceEdges G))
    (restoringIndependentProgram G).gates (0,1) [] C (by simpa only [List.append_nil] using hbit)
  have hsize : (circuitBits n (restoringIndependentProgram G).gates).length+2*restoringSwapPairs (sourceEdges G)+C≤
      sourceRegisterSize.eval (GraphInput.encode ⟨n,G⟩).length := by
    rw [sourceRegisterSize,eval_add]
    exact Nat.add_le_add_right (source_input_bound G) C
  have hm:=polynomial_nat_eval_mono (time p) hsize
  refine ⟨c,hc,hb.trans ?_⟩
  simpa only [sourceTime,eval_comp] using hm

lemma sourceResult_correct {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    (sourceResult hn G).2≠0 ∧ RationalAccumulator.value (sourceResult hn G)=(G.independentCount:ℚ) :=
  restoring_result_correct hn G
lemma sourceResult_division {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    (sourceResult hn G).2∣(sourceResult hn G).1 ∧ (sourceResult hn G).1/(sourceResult hn G).2=(G.independentCount:ℤ) :=
  restoring_result_division hn G
end HiddenCircuits.Circuit.Runtime.SourceOuter
