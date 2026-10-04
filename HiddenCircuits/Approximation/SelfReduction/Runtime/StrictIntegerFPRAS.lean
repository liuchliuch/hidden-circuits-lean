import HiddenCircuits.Approximation.SelfReduction.Runtime.StrictIntegerCountRuntime

/-! Native positive-radius strict integer-input FPRAS. The actual machine receives no
adjacency matrix or initializer; its fair-tape bound is polynomial in the
original integer-radius/precision request, with exact zero and empty semantics. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.StrictIntegerCounting
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
    SelfReduction.GraphCount.randomBitsPolynomial.eval (estimateInput (GraphReduction.Runtime.StrictInteger.bits xs) r k).length≤
      randomProgram.bits (estimateInput xs r k) := by
  have h:=polynomial_nat_eval_mono SelfReduction.GraphCount.randomBitsPolynomial (request_size (estimateInput xs r k))
  dsimp only at h
  rw [bits_eq]
  simpa only [request_canonical] using h
lemma canonical_bits_dominate (G : GraphInput) (R : StrictIntegerRepresentation G) (r k : ℕ) :
    SelfReduction.GraphCount.randomBitsPolynomial.eval (estimateInput G.encode r k).length≤
      randomProgram.bits (estimateInput (strictIntegerBits G R) r k) := by
  simpa only [GraphReduction.Runtime.StrictInteger.bits_representation] using bits_dominate (strictIntegerBits G R) r k
lemma run_canonical (G : GraphInput) (R : StrictIntegerRepresentation G) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput (strictIntegerBits G R) r k))) :
    randomProgram.run (estimateInput (strictIntegerBits G R) r k) tape=
      GraphCounting.evaluate (pairBits (estimateInput G.encode r k) (List.ofFn tape)) :=
  evaluate_canonical G R r k _

theorem approximationGuarantee :
    ApproximationGuarantee randomProgram SamplerRuntime.StrictIntegerSampler.promised strictIntegerProblem := by
  intro xs hx r k
  obtain ⟨G,R,rfl⟩:=hx
  rw [strictIntegerProblem_oracle G R]
  constructor
  · intro hz tape
    rw [run_canonical]
    exact GraphCounting.evaluate_zero_padded G r k _ hz
      (by simpa only [List.length_ofFn] using canonical_bits_dominate G R r k)
  · simp only [run_canonical]
    exact GraphCounting.evaluate_guarantee_padded G (SamplerRuntime.StrictIntegerSampler.quasimonotone G R) r k _
      (canonical_bits_dominate G R r k)

theorem exact_zero (G : GraphInput) (R : StrictIntegerRepresentation G) (r k : ℕ)
    (hz:perfectMatchingCount G.2.graph=0)
    (tape : CoinTape (randomProgram.bits (estimateInput (strictIntegerBits G R) r k))) :
    decodeEstimate (randomProgram.run (estimateInput (strictIntegerBits G R) r k) tape)=some 0 := by
  apply (approximationGuarantee _ ⟨G,R,rfl⟩ r k).1
  rw [strictIntegerProblem_oracle G R,hz]

theorem exact_empty (G : GraphInput) (R : StrictIntegerRepresentation G) (hG:G.1=0) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput (strictIntegerBits G R) r k))) :
    decodeEstimate (randomProgram.run (estimateInput (strictIntegerBits G R) r k) tape)=some 1 := by
  rw [run_canonical]
  exact GraphCounting.evaluate_empty_padded G hG r k _
    (by simpa only [List.length_ofFn] using canonical_bits_dominate G R r k)

theorem hasFPRAS : HasFPRAS SamplerRuntime.StrictIntegerSampler.promised strictIntegerProblem :=
  ⟨randomProgram,approximationGuarantee⟩
lemma raw_bits_dominate (xs : BitString) (r k : ℕ) :
    SelfReduction.GraphCount.randomBitsPolynomial.eval
      (estimateInput (GraphReduction.Runtime.StrictInteger.graphInput xs).encode r k).length≤
      randomProgram.bits (estimateInput xs r k) := by
  simpa only [GraphReduction.Runtime.StrictInteger.bits_graph] using bits_dominate xs r k
lemma run_raw (xs : BitString) (r k : ℕ) (tape : CoinTape (randomProgram.bits (estimateInput xs r k))) :
    randomProgram.run (estimateInput xs r k) tape=GraphCounting.evaluate
      (pairBits (estimateInput (GraphReduction.Runtime.StrictInteger.graphInput xs).encode r k) (List.ofFn tape)) :=
  evaluate_raw xs r k _

theorem exact_zero_raw (xs : BitString) (hz:strictIntegerProblem xs=0) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput xs r k))) :
    decodeEstimate (randomProgram.run (estimateInput xs r k) tape)=some 0 := by
  rw [run_raw]
  exact GraphCounting.evaluate_zero_padded (GraphReduction.Runtime.StrictInteger.graphInput xs) r k _
    ((strictIntegerProblem_exact xs).symm.trans hz)
    (by simpa only [List.length_ofFn] using raw_bits_dominate xs r k)

/-- The nonpositive-radius extension returns exact zero on every nonempty labelled list. -/
theorem nonpositive_nonempty (xs : BitString) (hr:GraphReduction.Runtime.StrictInteger.radius xs≤0)
    (hn:0<(LooseWordList.words (GraphReduction.Runtime.StrictInteger.data xs)).length) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput xs r k))) :
    decodeEstimate (randomProgram.run (estimateInput xs r k) tape)=some 0 :=
  exact_zero_raw xs (strictIntegerProblem_nonpositive_nonempty xs hr hn) r k tape

/-- Empty decoded lists return exact one, including radius0 and missing/malformed headers. -/
theorem exact_empty_raw (xs : BitString)
    (hn:(LooseWordList.words (GraphReduction.Runtime.StrictInteger.data xs)).length=0) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput xs r k))) :
    decodeEstimate (randomProgram.run (estimateInput xs r k) tape)=some 1 := by
  rw [run_raw]
  exact GraphCounting.evaluate_empty_padded (GraphReduction.Runtime.StrictInteger.graphInput xs) hn r k _
    (by simpa only [List.length_ofFn] using raw_bits_dominate xs r k)

end HiddenCircuits.Approximation.SelfReduction.Runtime.StrictIntegerCounting
