import HiddenCircuits.Complexity.CNFEncoding
import HiddenCircuits.Complexity.RecoveryBitBounds

/-! Executable high-level source oracle algorithm. Its query strings, arithmetic,
exact result, and bit bounds are proved. The separate compilation to the finite
binary-stack oracle-machine model is not silently assumed. -/
namespace HiddenCircuits.Complexity

/-- Parse, issue ordinary binary graph queries, and perform integer-only recovery. -/
def satViaIndependentOracle (oracle : BitString → ℕ) (input : BitString) : ℕ :=
  match CNFInput.decode input with
  | none => 0
  | some F => recoverIntegerGrid F.1 F.2.1 (fun i j =>
      (oracle (F.2.2.encodedCloneQuery i.val j.val) : ℤ))

/-- Correct for every binary input, including malformed strings. -/
theorem satViaIndependentOracle_correct (input : BitString) :
    satViaIndependentOracle GraphInput.independentSetProblem input = CNFInput.satProblem input := by
  unfold satViaIndependentOracle CNFInput.satProblem
  cases h : CNFInput.decode input with
  | none => rfl
  | some F => exact F.2.2.recoverIntegerGrid_encoded_correct

namespace CNFInput

theorem interpolation_exponents_in_source_bits (F : CNFInput) :
    denominatorExponent F.1 F.2.1 ≤ 2*(encode F).length^3 ∧
    numeratorExponent F.1 F.2.1 ((2*F.1+F.2.1)^2+1) ≤ 5*(encode F).length^3 := by
  let L := (encode F).length
  have hlen : 2*F.1+F.2.1+1 ≤ L := encode_length_lower F
  have hn : F.1+1 ≤ L := by omega
  have hm : F.2.1+1 ≤ L := by omega
  have hL : 1 ≤ L := by omega
  have hn2 : F.1^2+1 ≤ L^2 := by
    have h := Nat.pow_le_pow_left hn 2
    nlinarith
  have hm2 : F.2.1^2+1 ≤ L^2 := by
    have h := Nat.pow_le_pow_left hm 2
    nlinarith
  have hx : (F.1^2+1)*(F.1+1) ≤ L^3 := by
    have h := Nat.mul_le_mul hn2 hn
    nlinarith [show L^2*L=L^3 by ring]
  have hy : (F.2.1^2+1)*(F.2.1+1) ≤ L^3 := by
    have h := Nat.mul_le_mul hm2 hm
    nlinarith [show L^2*L=L^3 by ring]
  have hB : (2*F.1+F.2.1)^2+1 ≤ L^2 := by
    have h := Nat.pow_le_pow_left hlen 2
    nlinarith
  have hgrid : (F.1+1)*(F.2.1+1) ≤ L^2 := by
    simpa [pow_two] using Nat.mul_le_mul hn hm
  have hp : L^2 ≤ L^3 := Nat.pow_le_pow_right hL (by decide)
  constructor
  · unfold denominatorExponent
    change _ ≤ 2*L^3
    omega
  · unfold numeratorExponent denominatorExponent
    change _ ≤ 5*L^3
    omega

/-- Both real interpolation accumulators have cubic magnitude-bit bounds in the
actual binary CNF input length. -/
theorem recovery_bits_in_source_bits (F : CNFInput) :
    (gridDenominator F.1 F.2.1).natAbs.size ≤ 3*(encode F).length^3 ∧
    (gridNumerator F.1 F.2.1
      (fun i j => (F.2.2.cloneCount i.val j.val : ℤ))).natAbs.size ≤ 6*(encode F).length^3 := by
  have hb := F.2.2.source_recovery_accumulator_bits
  have he := interpolation_exponents_in_source_bits F
  have hL : 1 ≤ (encode F).length := by have := encode_length_lower F; omega
  have hp : 1 ≤ (encode F).length^3 := Nat.one_le_pow _ _ hL
  constructor <;> omega

end CNFInput
end HiddenCircuits.Complexity
