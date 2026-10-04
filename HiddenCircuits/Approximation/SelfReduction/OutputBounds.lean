import HiddenCircuits.Approximation.SelfReduction.EncodedOutput

/-! Every output and intermediate arithmetic value has a polynomial bit bound,
including on statistically bad random tapes. -/
namespace HiddenCircuits.Approximation.SelfReduction
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic

 theorem natural_product_bound (xs : List ℕ) (B : ℕ) (hx : ∀ x ∈ xs, x ≤ 2^B) :
    xs.prod ≤ 2^(B*xs.length) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hx x (by simp)
    have ht := ih (fun y hy => hx y (by simp [hy]))
    calc
      (x::xs).prod = x*xs.prod := rfl
      _ ≤ 2^B*2^(B*xs.length) := Nat.mul_le_mul hh ht
      _ = _ := by simp only [List.length_cons]; rw [← pow_add]; congr 1; ring

 theorem binary_word_bound (n B : ℕ) (hn : n ≤ 2^B) :
    (Computability.encodeNat n).length ≤ B+1 := by
  have h := signedBits_length_of_abs_bound (z := (n : ℤ)) (E := B) (by simpa using hn)
  simp only [signedBits, List.length_cons, Int.natAbs_natCast] at h
  omega

 theorem encodeRatio_length (a b B : ℕ) (ha : a ≤ 2^B) (hb : b ≤ 2^B) :
    (encodeRatio a b).length ≤ 3*B+4 := by
  by_cases hz : b=0
  · simp [encodeRatio, hz, encodeNat_length]
  · have han := binary_word_bound a B ha
    have hbn := binary_word_bound (b-1) B ((Nat.sub_le b 1).trans hb)
    simp only [encodeRatio, if_neg hz, pairBits_length]
    omega

/-- Both components of the unreduced rational output have O(Bd) bits. -/
theorem reciprocalProductOutput_length (M B : ℕ) (counts : List ℕ)
    (hM : M ≤ 2^B) (hc : ∀ c ∈ counts, c ≤ 2^B) :
    (reciprocalProductOutput M counts).length ≤ 3*B*counts.length+4 := by
  have hnum : M^counts.length ≤ 2^(B*counts.length) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hM counts.length
  have hden := natural_product_bound counts B hc
  have h := encodeRatio_length (M^counts.length) counts.prod (B*counts.length) hnum hden
  simpa [reciprocalProductOutput, mul_assoc] using h

/-- All random outcomes have polynomial-length binary outputs, not merely the
successful outcomes. M itself is polynomial in inverse requested accuracy. -/
theorem countingOutput_length {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (r : Fin d → StageTape α T k) :
    (countingOutput R sampler T k d s r).length ≤ 3*batchSize T*d+4 := by
  have hM := nat_le_two_pow (batchSize T)
  have h := reciprocalProductOutput_length (batchSize T) (batchSize T)
    (selectedCounts R sampler T k d s r) hM
    (fun c hc => (selectedCounts_bound R sampler T k d s r c hc).trans hM)
  simpa [countingOutput] using h

/-- The actual denominator multiplication receives only the observed bounded
counts and has a verified finite bit-stack execution on every random outcome. -/
theorem counting_denominator_executes {S α : Type*} {b : ℕ} (R : CountReduction S b)
    (sampler : S → α → Option (Fin (b+1))) (T k d : ℕ) (s : S) (r : Fin d → StageTape α T k)
    (g : BitString → ℕ) :
    ∃ t, productAccumulator.Executes g
      (productStore (signedBits 1) [] [] [] [] []
        (encodeBitList ((selectedCounts R sampler T k d s r).map fun c : ℕ => signedBits (c : ℤ))))
      (productStore (signedBits ((selectedCounts R sampler T k d s r).prod : ℤ)) [] [] [] [] [] []) t ∧
      t ≤ 1+d*productIterationBound (batchSize T*d+2) := by
  have h := denominatorProduct_executes g (selectedCounts R sampler T k d s r) (batchSize T)
    (fun c hc => (selectedCounts_bound R sampler T k d s r c hc).trans (nat_le_two_pow _))
  simpa using h

/-- The matching numerator is likewise computed by a fixed finite binary loop. -/
theorem counting_numerator_executes (g : BitString → ℕ) (T d : ℕ) :
    ∃ t, productAccumulator.Executes g
      (productStore (signedBits 1) [] [] [] [] []
        (encodeBitList (List.replicate d (signedBits (batchSize T : ℤ)))))
      (productStore (signedBits ((batchSize T : ℤ)^d)) [] [] [] [] [] []) t ∧
      t ≤ 1+d*productIterationBound (batchSize T*d+2) :=
  numeratorProduct_executes g (batchSize T) d (batchSize T) (nat_le_two_pow _)

end HiddenCircuits.Approximation.SelfReduction
