import HiddenCircuits.Circuit.Runtime.SourceOuterRuntime

/-! The accumulator produced by the actual three nested
loops has the restoring source count as its exact rational value. -/
namespace HiddenCircuits.Circuit.Runtime.SourceOuter
open HiddenCircuits.Complexity BinaryArithmetic

lemma restoring_result_correct {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    let acc:=result hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates (0,1)
    acc.2≠0 ∧ RationalAccumulator.value acc=(G.independentCount:ℚ) :=
  ⟨SourceSampleIntegers.restoring_run_nonzero hn G,SourceSampleIntegers.restoring_run_value hn G⟩
lemma restoring_result_division {n : ℕ} (hn : 0<n) (G : MatrixGraph n) :
    let acc:=result hn (2*restoringSwapPairs (sourceEdges G)) (restoringIndependentProgram G).gates (0,1)
    acc.2∣acc.1 ∧ acc.1/acc.2=(G.independentCount:ℤ) := SourceSampleIntegers.restoring_run_division hn G
end HiddenCircuits.Circuit.Runtime.SourceOuter
