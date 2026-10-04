import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorBounds
import HiddenCircuits.Approximation.Schemes

/-! Finite binary arithmetic for reciprocal-frequency products. The numerator
and denominator are computed by real query-free bit-stack programs, and every
intermediate bit bound is discharged from empirical-count bounds. -/
namespace HiddenCircuits.Approximation.SelfReduction
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic

/-- A total binary rational encoding. Zero denominator returns exact zero. -/
def encodeRatio (a b : ℕ) : BitString :=
  if b=0 then pairBits (Computability.encodeNat 0) (Computability.encodeNat 0)
  else pairBits (Computability.encodeNat a) (Computability.encodeNat (b-1))

@[simp] theorem decodeEstimate_encodeRatio (a b : ℕ) :
    decodeEstimate (encodeRatio a b) = some ((a : ℚ)/b) := by
  by_cases hb : b=0
  · simp [encodeRatio, hb, decodeEstimate]
  · have hb' : b-1+1=b := by omega
    have hc : ((b-1 : ℕ) : ℚ)+1=(b : ℚ) := by exact_mod_cast hb'
    simp [encodeRatio, hb, decodeEstimate, hc]

/-- With common sample denominator M, no rational reduction or division is
needed: the output is `M^d / product empiricalCounts`. -/
def reciprocalProductOutput (M : ℕ) (counts : List ℕ) : BitString :=
  encodeRatio (M^counts.length) counts.prod

@[simp] theorem reciprocalProductOutput_value (M : ℕ) (counts : List ℕ) :
    decodeEstimate (reciprocalProductOutput M counts) =
      some ((M : ℚ)^counts.length/(counts.prod : ℚ)) := by
  simp [reciprocalProductOutput]

/-- Denominator multiplication is a fixed finite binary program. Its oracle
parameter is irrelevant because the accumulator is query-free. -/
theorem denominatorProduct_executes (g : BitString → ℕ) (counts : List ℕ) (B : ℕ)
    (hcounts : ∀ c ∈ counts, c ≤ 2^B) :
    ∃ t, productAccumulator.Executes g
      (productStore (signedBits 1) [] [] [] [] []
        (encodeBitList (counts.map fun c : ℕ => signedBits (c : ℤ))))
      (productStore (signedBits (counts.prod : ℤ)) [] [] [] [] [] []) t ∧
      t ≤ 1+counts.length*productIterationBound (B*counts.length+2) := by
  have h := productAccumulator_bounded g (counts.map (fun c : ℕ => (c : ℤ))) 1 0 B
    (by norm_num) (by
      intro z hz
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hz
      simpa using hcounts c hc)
  simpa [List.map_map, Function.comp_def, Nat.cast_list_prod] using h

/-- Numerator exponentiation is also implemented by the actual binary product
loop, rather than assumed unit-cost multiplication of arbitrary naturals. -/
theorem numeratorProduct_executes (g : BitString → ℕ) (M d B : ℕ) (hM : M ≤ 2^B) :
    ∃ t, productAccumulator.Executes g
      (productStore (signedBits 1) [] [] [] [] []
        (encodeBitList (List.replicate d (signedBits (M : ℤ)))))
      (productStore (signedBits ((M : ℤ)^d)) [] [] [] [] [] []) t ∧
      t ≤ 1+d*productIterationBound (B*d+2) := by
  have h := productAccumulator_bounded g (List.replicate d (M : ℤ)) 1 0 B
    (by norm_num) (by
      intro z hz
      have hz' : z = (M : ℤ) := List.eq_of_mem_replicate hz
      subst z
      simpa using hM)
  simpa using h

/-- Polynomial bound for both arithmetic loops when factor count and input bit
lengths are bounded by N. This charges the growing accumulator bit length. -/
theorem product_time_polynomial (d B N : ℕ) (hd : d ≤ N) (hB : B ≤ N) :
    1+d*productIterationBound (B*d+2) ≤
      1+N*(50*(2*(N^2+2)+1)^3+10*(N^2+2)+20) := by
  unfold productIterationBound
  gcongr
  · simpa [pow_two] using Nat.mul_le_mul hB hd
  · simpa [pow_two] using Nat.mul_le_mul hB hd

end HiddenCircuits.Approximation.SelfReduction
