import HiddenCircuits.Approximation.FiniteCoins

/-!
# Machine-grounded approximation specifications

A random-bit program is a genuine polynomial-time finite TM2 computation with
an explicitly polynomial number of fair random bits. The probability space is
finite; neither exact real random numbers nor uncharged operations are used.

These are specifications, not existence theorems for the paper's graph classes.
No prior mixing or approximation result is postulated here.
-/
namespace HiddenCircuits.Approximation
open HiddenCircuits.Complexity
attribute [local instance] Classical.propDecidable

/-- A finite polynomial-time machine supplied with a finite uniform random tape.
`PolyTime` unfolds to mathlib's finite TM2 machine and operational time bound. -/
structure RandomBitProgram where
  evaluate : BitString → BitString
  polynomialTime : PolyTime evaluate
  randomBits : Polynomial ℕ

namespace RandomBitProgram

def bits (A : RandomBitProgram) (input : BitString) : ℕ := A.randomBits.eval input.length

def run (A : RandomBitProgram) (input : BitString) (r : CoinTape (A.bits input)) : BitString :=
  A.evaluate (pairBits input (List.ofFn r))

/-- The deterministic machine sees the input and every random bit explicitly. -/
theorem encoded_input_length (A : RandomBitProgram) (input : BitString)
    (r : CoinTape (A.bits input)) :
    (pairBits input (List.ofFn r)).length = 2*input.length+A.randomBits.eval input.length+1 := by
  simp [bits]

/-- The actual combined input length is polynomial in the original input length. -/
theorem encoded_input_polynomial (A : RandomBitProgram) (input : BitString)
    (r : CoinTape (A.bits input)) :
    (pairBits input (List.ofFn r)).length =
      (2*Polynomial.X+A.randomBits+1).eval input.length := by
  simp [bits]

end RandomBitProgram

/-- Unary precision is necessary: time polynomial in `k` is time polynomial in
`log(1/epsilon)` when the sampling tolerance is `2^(-k)`. -/
def sampleInput (x : BitString) (k : ℕ) : BitString := pairBits x (List.replicate k true)

/-- Unary inverse relative accuracy and unary confidence precision. -/
def estimateInput (x : BitString) (r k : ℕ) : BitString :=
  pairBits x (pairBits (List.replicate r true) (List.replicate k true))

@[simp] theorem sampleInput_length (x : BitString) (k : ℕ) :
    (sampleInput x k).length = 2*x.length+k+1 := by simp [sampleInput]

@[simp] theorem estimateInput_length (x : BitString) (r k : ℕ) :
    (estimateInput x r k).length = 2*x.length+2*r+k+2 := by
  simp [estimateInput]
  omega

/-- The failure/empty-instance marker is different from every witness, including
an empty witness. A leading `true` is a successful sample. -/
def decodeSample : BitString → Option BitString
  | true :: w => some w
  | _ => none

/-- Binary rational output with a natural numerator and a positive denominator. -/
def decodeEstimate (s : BitString) : Option ℚ := do
  let (a,b) ← unpairBits s
  pure ((Computability.decodeNat a : ℚ)/(Computability.decodeNat b+1 : ℕ))

/-- Exact target probability. Empty solution sets have the single outcome `none`;
nonempty sets have uniform mass on their distinct witnesses. -/
noncomputable def uniformProbability (W : Finset BitString) (E : Option BitString → Prop) : ℚ :=
  if W.card=0 then (if E none then 1 else 0)
  else ((W.filter (fun w => E (some w))).card : ℚ)/W.card

@[simp] theorem uniformProbability_empty (E : Option BitString → Prop) :
    uniformProbability ∅ E = if E none then 1 else 0 := by simp [uniformProbability]

theorem uniformProbability_nonempty_none {W : Finset BitString} (hW : W.Nonempty) :
    uniformProbability W (fun z => z=none) = 0 := by
  simp [uniformProbability,Finset.card_ne_zero.mpr hW]

@[simp] theorem uniformProbability_true (W : Finset BitString) :
    uniformProbability W (fun _ => True) = 1 := by
  by_cases h : W.card=0
  · simp [uniformProbability,h]
  · simp [uniformProbability,h]

/-- A concrete sampler's finite distribution is within total variation `2^-k`.
The event characterization measures the *unconditional* output distribution,
so failure probability cannot be discarded by conditioning it away. -/
def SamplingGuarantee (A : RandomBitProgram) (promised : BitString → Prop)
    (solutions : BitString → Finset BitString) : Prop :=
  ∀ x, promised x → ∀ k,
    (∀ r w, decodeSample (A.run (sampleInput x k) r)=some w → w∈solutions x) ∧
    (solutions x=∅ → ∀ r, decodeSample (A.run (sampleInput x k) r)=none) ∧
    ∀ E : Option BitString → Prop,
      |coinProbability (A.bits (sampleInput x k))
          (fun r => E (decodeSample (A.run (sampleInput x k) r))) -
        uniformProbability (solutions x) E| ≤ 1/(2^k : ℚ)

/-- FPAUS existence requires an actual finite polynomial-time random-bit program. -/
def HasFPAUS (promised : BitString → Prop) (solutions : BitString → Finset BitString) : Prop :=
  ∃ A : RandomBitProgram, SamplingGuarantee A promised solutions

/-- A relative approximation, with exact zero as the only successful value when
the count is zero. -/
def RelativeEstimate (N r : ℕ) (z : ℚ) : Prop := |z-N| ≤ (N:ℚ)/(r+1)

@[simp] theorem relativeEstimate_zero (r : ℕ) (z : ℚ) :
    RelativeEstimate 0 r z ↔ z=0 := by simp [RelativeEstimate]

/-- Success probability at least `1-2^-k`, relative error `1/(r+1)`, and exact
zero output on zero-count promised instances. In particular `k=2` gives `3/4`.
There is no promise that the count is nonzero. -/
def ApproximationGuarantee (A : RandomBitProgram) (promised : BitString → Prop)
    (count : BitString → ℕ) : Prop :=
  ∀ x, promised x → ∀ r k,
    (count x=0 → ∀ tape, decodeEstimate (A.run (estimateInput x r k) tape)=some 0) ∧
    1-1/(2^k : ℚ) ≤ coinProbability (A.bits (estimateInput x r k))
      (fun tape => ∃ z, decodeEstimate (A.run (estimateInput x r k) tape)=some z ∧
        RelativeEstimate (count x) r z)

/-- Amplified FPRAS existence, grounded in the same finite machine model. -/
def HasFPRAS (promised : BitString → Prop) (count : BitString → ℕ) : Prop :=
  ∃ A : RandomBitProgram, ApproximationGuarantee A promised count

theorem ApproximationGuarantee.three_quarters {A : RandomBitProgram}
    {promised : BitString → Prop} {count : BitString → ℕ}
    (h : ApproximationGuarantee A promised count) (x : BitString) (hx : promised x) (r : ℕ) :
    (3/4 : ℚ) ≤ coinProbability (A.bits (estimateInput x r 2))
      (fun tape => ∃ z, decodeEstimate (A.run (estimateInput x r 2) tape)=some z ∧
        RelativeEstimate (count x) r z) := by
  have hs := (h x hx r 2).2
  norm_num at hs ⊢
  exact hs

/-- The accuracy estimate also bounds unconditional failure of a nonempty sampler. -/
theorem SamplingGuarantee.failure_bound {A : RandomBitProgram}
    {promised : BitString → Prop} {solutions : BitString → Finset BitString}
    (h : SamplingGuarantee A promised solutions) (x : BitString) (hx : promised x)
    (hW : (solutions x).Nonempty) (k : ℕ) :
    coinProbability (A.bits (sampleInput x k))
      (fun r => decodeSample (A.run (sampleInput x k) r)=none) ≤ 1/(2^k : ℚ) := by
  have hs := (h x hx k).2.2 (fun z => z=none)
  rw [uniformProbability_nonempty_none hW, sub_zero,
    abs_of_nonneg (coinProbability_nonneg _ _)] at hs
  exact hs

end HiddenCircuits.Approximation
