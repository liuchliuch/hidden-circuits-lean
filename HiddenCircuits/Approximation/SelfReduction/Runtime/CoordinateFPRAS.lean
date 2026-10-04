import HiddenCircuits.Approximation.SelfReduction.Runtime.CoordinateCountRuntime

/-! Native Corollary1.3 coordinate-input FPRAS. The actual machine receives no
adjacency matrix or initializer; its fair-tape bound is polynomial in the
original coordinate/precision request, with exact zero and empty semantics. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.CoordinateCounting
open Complexity GraphReduction Polynomial

noncomputable def bitsPolynomial : Polynomial ℕ := SelfReduction.GraphCount.randomBitsPolynomial.comp requestSize
noncomputable def randomProgram : RandomBitProgram where
  evaluate:=evaluate
  polynomialTime:=evaluate_polyTime
  randomBits:=bitsPolynomial
lemma bits_eq (input : BitString) : randomProgram.bits input=
    SelfReduction.GraphCount.randomBitsPolynomial.eval (requestSize.eval input.length) := by
  simp only [randomProgram,RandomBitProgram.bits,bitsPolynomial,eval_comp]
lemma bits_dominate (xs : BitString) (r k : ℕ) :
    SelfReduction.GraphCount.randomBitsPolynomial.eval (estimateInput (GraphReduction.Runtime.CoordinateGraph.bits xs) r k).length≤
      randomProgram.bits (estimateInput xs r k) := by
  have h:=polynomial_nat_eval_mono SelfReduction.GraphCount.randomBitsPolynomial (request_size (estimateInput xs r k))
  dsimp only at h
  rw [bits_eq]
  simpa only [request_canonical] using h
lemma canonical_bits_dominate (G : GraphInput) (R : UnitIntegerRepresentation G) (r k : ℕ) :
    SelfReduction.GraphCount.randomBitsPolynomial.eval (estimateInput G.encode r k).length≤
      randomProgram.bits (estimateInput (unitCoordinateBits G R) r k) := by
  simpa only [GraphReduction.Runtime.CoordinateGraph.bits_representation] using bits_dominate (unitCoordinateBits G R) r k
lemma run_canonical (G : GraphInput) (R : UnitIntegerRepresentation G) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput (unitCoordinateBits G R) r k))) :
    randomProgram.run (estimateInput (unitCoordinateBits G R) r k) tape=
      GraphCounting.evaluate (pairBits (estimateInput G.encode r k) (List.ofFn tape)) :=
  evaluate_canonical G R r k _

theorem approximationGuarantee :
    ApproximationGuarantee randomProgram SamplerRuntime.CoordinateSampler.promised unitCoordinateProblem := by
  intro xs hx r k
  obtain ⟨G,R,rfl⟩:=hx
  rw [unitCoordinateProblem_oracle G R]
  constructor
  · intro hz tape
    rw [run_canonical]
    exact GraphCounting.evaluate_zero_padded G r k _ hz
      (by simpa only [List.length_ofFn] using canonical_bits_dominate G R r k)
  · simp only [run_canonical]
    exact GraphCounting.evaluate_guarantee_padded G (SamplerRuntime.CoordinateSampler.quasimonotone G R) r k _
      (canonical_bits_dominate G R r k)

theorem exact_zero (G : GraphInput) (R : UnitIntegerRepresentation G) (r k : ℕ)
    (hz:perfectMatchingCount G.2.graph=0)
    (tape : CoinTape (randomProgram.bits (estimateInput (unitCoordinateBits G R) r k))) :
    decodeEstimate (randomProgram.run (estimateInput (unitCoordinateBits G R) r k) tape)=some 0 := by
  apply (approximationGuarantee _ ⟨G,R,rfl⟩ r k).1
  rw [unitCoordinateProblem_oracle G R,hz]

theorem exact_empty (G : GraphInput) (R : UnitIntegerRepresentation G) (hG:G.1=0) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput (unitCoordinateBits G R) r k))) :
    decodeEstimate (randomProgram.run (estimateInput (unitCoordinateBits G R) r k) tape)=some 1 := by
  rw [run_canonical]
  exact GraphCounting.evaluate_empty_padded G hG r k _
    (by simpa only [List.length_ofFn] using canonical_bits_dominate G R r k)

theorem hasFPRAS : HasFPRAS SamplerRuntime.CoordinateSampler.promised unitCoordinateProblem :=
  ⟨randomProgram,approximationGuarantee⟩
end HiddenCircuits.Approximation.SelfReduction.Runtime.CoordinateCounting
