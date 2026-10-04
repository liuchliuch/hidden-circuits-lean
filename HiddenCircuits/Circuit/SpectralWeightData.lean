import HiddenCircuits.Circuit.SpectralIntegerWeights
import HiddenCircuits.Circuit.IntegerRatioAccumulator

/-! Explicit bounded integer numerator/denominator output for every Section7 spectral coefficient. -/
namespace HiddenCircuits.Circuit
open scoped BigOperators
open IntegerRatioAccumulator

/-- Uses the cached integer polynomial-product array, rather than recursive coefficient expansion. -/
def spectralWeightedNumerator (g : ℕ) (z : ℤ) (k : ℕ) (i : SpectralIndex g) : ℤ :=
  z^(g-i.1.val-i.2.val)*HiddenCircuits.DH.ArrayColumn.read (spectralBasisArray g i).value k

/-- One integer pair represents the exact coefficient, without intermediate rational arithmetic. -/
def spectralWeightData (g : ℕ) (z : ℤ) (k : ℕ) : ℤ × ℤ :=
  (commonNumerator (spectralIndices g) (spectralWeightedNumerator g z k) (spectralBasisDenominator g),
    commonDenominator (spectralIndices g) (spectralBasisDenominator g))

/-- The full explicit coefficient vector used by the recovery formula. -/
def spectralWeightArray (g : ℕ) (z : ℤ) : Array (ℤ × ℤ) :=
  Array.ofFn (fun k : Fin (Fintype.card (SpectralIndex g)) => spectralWeightData g z k.val)

@[simp] theorem spectralWeightArray_size (g : ℕ) (z : ℤ) :
    (spectralWeightArray g z).size=Fintype.card (SpectralIndex g) := by simp [spectralWeightArray]

 theorem spectralWeightData_denominator_ne_zero (g : ℕ) (z : ℤ) (k : ℕ) :
    (spectralWeightData g z k).2≠0 :=
  commonDenominator_ne_zero _ _ (spectralBasisDenominator_ne_zero g)

/-- Exact agreement with the actual interpolating polynomial coefficient used in the circuit proof. -/
theorem spectralWeightData_correct (g : ℕ) (z : ℤ) (k : ℕ) :
    ((spectralWeightData g z k).1:ℚ)/((spectralWeightData g z k).2:ℚ)=targetCoefficient g (z:ℚ) k := by
  rw [spectralWeightData,ratio_correct _ (spectralIndices_nodup g) (mem_spectralIndices g)
    _ _ (spectralBasisDenominator_ne_zero g),targetCoefficient_integer_weights]
  apply Finset.sum_congr rfl
  intro i _
  rw [spectralWeightedNumerator,spectralBasisArray_read]
  push_cast
  ring

 def spectralBasisBitBound (g : ℕ) : ℕ := (4*g+1)*(g+1)^2+2

 theorem spectralBasisNumerator_envelope (g : ℕ) (i : SpectralIndex g) (k : ℕ) :
    (spectralBasisNumerator g i k).natAbs ≤ 2^(spectralBasisBitBound g) := by
  exact (Nat.size_le.mp (Nat.le_trans (Nat.le_succ _) (spectralBasis_bits g i k).1)).le

 theorem spectralBasisDenominator_envelope (g : ℕ) (i : SpectralIndex g) :
    (spectralBasisDenominator g i).natAbs ≤ 2^(spectralBasisBitBound g) := by
  exact (Nat.size_le.mp (Nat.le_trans (Nat.le_succ _) (spectralBasis_bits g i 0).2)).le

 theorem spectralWeightedNumerator_envelope (g : ℕ) (z : ℤ) (hz : z.natAbs ≤ 1)
    (k : ℕ) (i : SpectralIndex g) :
    (spectralWeightedNumerator g z k i).natAbs ≤ 2^(spectralBasisBitBound g) := by
  rw [spectralWeightedNumerator,spectralBasisArray_read,Int.natAbs_mul,Int.natAbs_pow]
  have hp : z.natAbs^(g-i.1.val-i.2.val) ≤ 1 := by
    simpa using Nat.pow_le_pow_left hz (g-i.1.val-i.2.val)
  exact (Nat.mul_le_mul hp (spectralBasisNumerator_envelope g i k)).trans_eq (one_mul _)

/-- Both integer components have polynomial bit length for each required target z=0 or z=-1. -/
theorem spectralWeightData_bits (g : ℕ) (z : ℤ) (hz : z.natAbs ≤ 1) (k : ℕ) :
    (spectralWeightData g z k).2.natAbs.size ≤ spectralBasisBitBound g*(g+1)^2+1 ∧
      (spectralWeightData g z k).1.natAbs.size ≤
        spectralBasisBitBound g+(spectralBasisBitBound g+1)*(g+1)^2+1 := by
  have hh := accumulator_bits (spectralIndices g) (spectralIndices_nodup g) (mem_spectralIndices g)
    (spectralWeightedNumerator g z k) (spectralBasisDenominator g)
    (spectralBasisBitBound g) (spectralBasisBitBound g)
    (spectralWeightedNumerator_envelope g z hz k) (spectralBasisDenominator_envelope g)
  have hc := spectralIndex_card_bound g
  constructor
  · exact hh.1.trans (by gcongr)
  · apply hh.2.trans
    nlinarith [Nat.mul_le_mul_left (spectralBasisBitBound g) hc]

end HiddenCircuits.Circuit
