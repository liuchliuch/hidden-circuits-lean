import HiddenCircuits.Circuit.Runtime.SpectralWeightsUnary

/-! Consumer identities for the exact numerator stream and the single common
denominator emitted by the fixed finite program. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralWeightsProgram
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic
open SpectralWeights

 theorem output_denominator_ne_zero (g : ℕ) : denominator g≠0 := denominator_ne_zero g

 theorem output_numerator (g : ℕ) (mode : Bool) (k : Fin (Fintype.card (SpectralIndex g))) :
    (vector g (SpectralTargets.base mode) (spectralIndices g))[k.val]'(by simp)=
      (spectralWeightData g (SpectralTargets.base mode) k.val).1 := by
  rw [vector_get g (SpectralTargets.base mode) (spectralIndices g) k.val k.isLt]
  simp only [term_eq,spectralWeightData,IntegerRatioAccumulator.commonNumerator]

 theorem output_coefficient_correct (g : ℕ) (mode : Bool) (k : Fin (Fintype.card (SpectralIndex g))) :
    ((vector g (SpectralTargets.base mode) (spectralIndices g))[k.val]'(by simp):ℚ)/(denominator g:ℚ)=
      targetCoefficient g (SpectralTargets.base mode:ℚ) k.val := by
  rw [output_numerator,denominator_data g (SpectralTargets.base mode) k.val]
  exact spectralWeightData_correct g (SpectralTargets.base mode) k.val
end HiddenCircuits.Circuit.Runtime.SpectralWeightsProgram
