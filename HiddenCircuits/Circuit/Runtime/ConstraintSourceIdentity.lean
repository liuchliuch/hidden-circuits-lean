import HiddenCircuits.Complexity.ConstraintEncoding
import HiddenCircuits.Circuit.Runtime.SourceMetadata

/-! The direct Proposition8.1 source query is a literal native constraint-circuit
input. Its canonical rational oracle response has denominator1 and a polynomial
size integer numerator; normalization uses the actual restoring-route scalar. -/
namespace HiddenCircuits.Circuit.Runtime.ConstraintSource
open Complexity BinaryArithmetic

def exponent {n : ℕ} (G : MatrixGraph n) : ℕ := 2*restoringSwapPairs (sourceEdges G)
def query {n : ℕ} (G : MatrixGraph n) : ConstraintInput :=
  ⟨n,(restoringIndependentProgram G).gates,zeroBits n,zeroBits n⟩
noncomputable def numerator {n : ℕ} (G : MatrixGraph n) : ℤ := (G.independentCount:ℤ)*(2:ℤ)^(3*exponent G)
lemma normalization (a : ℕ) : (1/8:ℚ)^a=((2:ℚ)^(3*a))⁻¹ := by
  rw [pow_mul]
  norm_num
  simp [inv_pow]
lemma query_value {n : ℕ} (G : MatrixGraph n) : (query G).value=(numerator G:ℚ) := by
  have h:=restoringIndependentProgram_correct G
  change (restoringIndependentProgram G).scalar*constraintCircuitMatrix (restoringIndependentProgram G).gates (zeroBits n) (zeroBits n)=(G.independentCount:ℚ) at h
  rw [restoringIndependentProgram_scalar] at h
  change (1/8:ℚ)^(exponent G)*(query G).value=(G.independentCount:ℚ) at h
  rw [normalization] at h
  have hp:(2:ℚ)^(3*exponent G)≠0:=pow_ne_zero _ (by norm_num)
  have hh:=congrArg (fun z=>(2:ℚ)^(3*exponent G)*z) h
  simp only [←mul_assoc,mul_inv_cancel₀ hp,one_mul] at hh
  rw [hh]
  simp [numerator,mul_comm]
lemma query_num {n : ℕ} (G : MatrixGraph n) : (query G).value.num=numerator G := by rw [query_value];simp
lemma query_den {n : ℕ} (G : MatrixGraph n) : (query G).value.den=1 := by rw [query_value];simp
lemma numerator_bound {n : ℕ} (G : MatrixGraph n) : (numerator G).natAbs ≤ 2^(n+3*exponent G) := by
  simp only [numerator,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_pow,show Int.natAbs (2:ℤ)=2 from rfl,pow_add]
  exact Nat.mul_le_mul_right _ G.independentCount_le
lemma numerator_bits_bound {n : ℕ} (G : MatrixGraph n) :
    (signedBits (numerator G)).length ≤ n+3*exponent G+2 := signedBits_length_of_abs_bound (numerator_bound G)
lemma response_bits {n : ℕ} (G : MatrixGraph n) : RationalOracleEncoding.bits (query G).value=
    pairBits (signedBits (numerator G)) (signedBits (1:ℤ)) := by
  simp [RationalOracleEncoding.bits,query_num,query_den]
lemma response_length {n : ℕ} (G : MatrixGraph n) :
    (RationalOracleEncoding.bits (query G).value).length ≤ 2*n+6*exponent G+7 := by
  rw [response_bits,pairBits_length]
  have h:=numerator_bits_bound G
  have h1:(signedBits (1:ℤ)).length=2:=rfl
  rw [h1]
  omega
end HiddenCircuits.Circuit.Runtime.ConstraintSource
