import HiddenCircuits.Circuit.LagrangeIntegerArrays
import HiddenCircuits.Circuit.SharedDiagonal

/-! The shared-conjugation interpolation has explicit bounded integer weights at the actual powers-of-two nodes. -/
namespace HiddenCircuits.Circuit
open scoped BigOperators
open Polynomial
open LagrangeIntegerArrays IntegerSpectralWeights

def geometricIntegerNode {d : ℕ} (i : Fin (d+1)) : ℤ := 2^i.val

theorem geometricIntegerNode_injective (d : ℕ) : Function.Injective (@geometricIntegerNode d) := by
  intro i j h
  apply geometricNode_injective d
  change (2:ℚ)^i.val=(2:ℚ)^j.val
  change (2:ℤ)^i.val=(2:ℤ)^j.val at h
  exact_mod_cast h

 theorem geometricIntegerNode_bound {d : ℕ} (i : Fin (d+1)) :
    (geometricIntegerNode i).natAbs ≤ 2^d := by
  simp only [geometricIntegerNode,Int.natAbs_pow]
  exact Nat.pow_le_pow_right (by decide) (by omega)

def geometricBasisDenominator (d : ℕ) (i : Fin (d+1)) : ℤ :=
  basisDenominator (List.finRange (d+1)) geometricIntegerNode i

/-- Evaluation at zero needs exactly the constant entry of each computed numerator array. -/
def geometricZeroNumerator (d : ℕ) (i : Fin (d+1)) : ℤ :=
  HiddenCircuits.DH.ArrayColumn.read
    (arrayRun (otherNodes (List.finRange (d+1)) geometricIntegerNode i)).value 0

 theorem geometricBasisDenominator_ne_zero (d : ℕ) (i : Fin (d+1)) :
    geometricBasisDenominator d i≠0 := basisDenominator_ne_zero _ _ (geometricIntegerNode_injective d) i

 theorem geometricZeroWeights_bits (d : ℕ) (i : Fin (d+1)) :
    (geometricZeroNumerator d i).natAbs.size+1 ≤ (d+1)^2+2 ∧
      (geometricBasisDenominator d i).natAbs.size+1 ≤ (d+1)^2+2 := by
  have hh := basis_bounds (List.finRange (d+1)) geometricIntegerNode d geometricIntegerNode_bound i 0
  simpa only [geometricZeroNumerator,arrayRun_read,geometricBasisDenominator,basisNumerator,
    List.length_finRange,pow_two] using hh

/-- Exact Section7.1 postprocessing through ratios of the actual integer arrays. -/
theorem geometricInterpolate_zero_integer_weights (d : ℕ) (values : Fin (d+1) → ℚ) :
    (geometricInterpolate d values).eval 0=
      ∑ i : Fin (d+1), values i*(geometricZeroNumerator d i:ℚ)/(geometricBasisDenominator d i:ℚ) := by
  have hh := interpolate_coefficient (List.finRange (d+1)) (List.nodup_finRange _)
    (fun i => by simp) geometricIntegerNode values 0
  have he : (fun i : Fin (d+1) => (geometricIntegerNode i:ℚ))=geometricNode := by
    funext i
    simp [geometricIntegerNode,geometricNode]
  rw [he] at hh
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  change (Lagrange.interpolate Finset.univ geometricNode values).coeff 0=_
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  simp only [geometricZeroNumerator,arrayRun_read,geometricBasisDenominator,basisNumerator,
    div_eq_mul_inv,mul_assoc]

end HiddenCircuits.Circuit
