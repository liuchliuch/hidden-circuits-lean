import HiddenCircuits.Circuit.Runtime.DeltaValueBounds

namespace HiddenCircuits.Circuit.Runtime.DeltaValues
open Complexity BinaryArithmetic
open scoped BigOperators

lemma integer_abs {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (integerMatrix w x y).natAbs ≤ 2^((n+4)*w.length) := by
  induction w generalizing x y with
  | nil=>simp [integerMatrix,Matrix.one_apply];split_ifs <;> norm_num
  | cons a w ih=>
    change ((gate a*integerMatrix w) x y).natAbs ≤ _
    calc
      _ ≤ ∑ z : CodeBits n, (gate a x z*integerMatrix w z y).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _z : CodeBits n,16*2^((n+4)*w.length) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (gate_abs a x z) (ih z y)
      _ = 2^n*(16*2^((n+4)*w.length)) := by simp
      _ = 2^((n+4)*(a::w).length) := by
        simp only [List.length_cons,Nat.mul_add,Nat.mul_one,pow_add]
        ring

lemma value_eq {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    deltaCircuitMatrix w x y=(integerMatrix w x y:ℚ)/(2:ℚ)^w.length := by
  rw [integer_cast];field_simp
lemma numerator_length {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (signedBits (deltaCircuitMatrix w x y).num).length ≤ (n+4)*w.length+2 := by
  let u:=integerMatrix w x y
  let v:ℤ:=2^w.length
  have hv:v≠0 := by dsimp [v];positivity
  have hval : deltaCircuitMatrix w x y=(u:ℚ)/(v:ℚ) := by simpa [u,v] using value_eq w x y
  rw [hval,RationalNormalize.numerator_eq u v hv,if_neg (by dsimp [v];exact not_lt.mpr (by positivity))]
  exact (RationalNormalize.quotient_bits_le u _).trans (signedBits_length_of_abs_bound (integer_abs w x y))
lemma denominator_length {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (signedBits ((deltaCircuitMatrix w x y).den:ℤ)).length ≤ w.length+2 := by
  let u:=integerMatrix w x y
  let v:ℤ:=2^w.length
  have hv:v≠0 := by dsimp [v];positivity
  have hval : deltaCircuitMatrix w x y=(u:ℚ)/(v:ℚ) := by simpa [u,v] using value_eq w x y
  rw [hval,RationalNormalize.denominator_eq u v hv,if_neg (by dsimp [v];exact not_lt.mpr (by positivity))]
  apply (RationalNormalize.quotient_bits_le v _).trans
  apply signedBits_length_of_abs_bound
  simp [v]
lemma rational_bits_length {n : ℕ} (w : List (DeltaGate n)) (x y : CodeBits n) :
    (RationalOracleEncoding.bits (deltaCircuitMatrix w x y)).length ≤ (2*n+9)*w.length+7 := by
  have hu:=numerator_length w x y
  have hv:=denominator_length w x y
  simp only [RationalOracleEncoding.bits,pairBits_length]
  nlinarith
end HiddenCircuits.Circuit.Runtime.DeltaValues
