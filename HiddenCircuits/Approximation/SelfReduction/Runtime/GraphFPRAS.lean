import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountingProgram

/-! Concrete general-graph FPRAS on the quasimonotone promise. The promise is
an analysis invariant only. The program takes raw graph bytes and unary
accuracy/confidence requests, uses a fixed polynomial fair tape, and handles
zero-count, odd-order, empty and malformed graphs with the specified outputs. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity SelfReduction.GraphCount

noncomputable def randomProgram : RandomBitProgram where
  evaluate := evaluate
  polynomialTime := evaluate_polyTime
  randomBits := randomBitsPolynomial

@[simp] lemma randomProgram_bits (request : BitString) :
    randomProgram.bits request=randomBitsPolynomial.eval request.length := rfl

lemma run_canonical (G : GraphInput) (r k : ℕ) (he : G.1%2=0)
    (tape : CoinTape (randomProgram.bits (estimateInput G.encode r k))) :
    randomProgram.run (estimateInput G.encode r k) tape=
      estimate (estimateInput G.encode r k).length G he (GraphCountSetup.canonical_bounds G r k).1 (List.ofFn tape) := by
  apply evaluate_canonical
  simp

lemma run_odd (G : GraphInput) (r k : ℕ) (he : G.1%2≠0)
    (tape : CoinTape (randomProgram.bits (estimateInput G.encode r k))) :
    randomProgram.run (estimateInput G.encode r k) tape=encodeRatio 0 0 :=
  evaluate_odd G r k _ he

lemma count_encode (G : GraphInput) :
    GraphInput.perfectMatchingProblem G.encode=perfectMatchingCount G.2.graph := by
  simp [GraphInput.perfectMatchingProblem,GraphInput.decode_encode]

/-- Exact zero on every tape is independent of the quasimonotone promise. -/
theorem exact_zero (G : GraphInput) (r k : ℕ) (hz : perfectMatchingCount G.2.graph=0)
    (tape : CoinTape (randomProgram.bits (estimateInput G.encode r k))) :
    decodeEstimate (randomProgram.run (estimateInput G.encode r k) tape)=some 0 := by
  by_cases he : G.1%2=0
  · rw [run_canonical G r k he]
    exact estimate_zero _ G he (GraphCountSetup.canonical_bounds G r k).1 hz _
  · rw [run_odd G r k he]
    simp

/-- The actual finite encoded machine satisfies unconditional amplified
relative accuracy and exact zero on all zero-count promised instances. -/
theorem approximationGuarantee :
    ApproximationGuarantee randomProgram SamplerRuntime.GraphFunctional.promised GraphInput.perfectMatchingProblem := by
  intro x hx r k
  obtain ⟨G,rfl,hclass⟩ := hx
  rw [count_encode]
  constructor
  · exact exact_zero G r k
  · by_cases he : G.1%2=0
    · simp only [randomProgram_bits]
      simp_rw [run_canonical G r k he]
      have hb := GraphCountSetup.canonical_bounds G r k
      exact estimate_guarantee _ G he hb.1 hclass r k hb.2.1 hb.2.2
    · have hz := perfectMatchingCount_zero_of_odd G.2.graph he
      have hevent : (fun tape : CoinTape (randomProgram.bits (estimateInput G.encode r k)) =>
          ∃z,decodeEstimate (randomProgram.run (estimateInput G.encode r k) tape)=some z ∧
            RelativeEstimate (perfectMatchingCount G.2.graph) r z)=(fun _ => True) := by
        funext tape;apply propext
        simp [run_odd G r k he,hz]
      rw [hevent,coinProbability_true]
      have hp : (0 : ℚ)≤1/2^k := by positivity
      linarith


/-- In particular, the physically rejected one-vertex input is exactly zero. -/
lemma run_order_one (G : GraphInput) (hG : G.1=1) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput G.encode r k))) :
    randomProgram.run (estimateInput G.encode r k) tape=encodeRatio 0 0 :=
  run_odd G r k (by omega) tape

/-- The empty graph takes zero sampling stages and returns exactly one. -/
lemma exact_empty (G : GraphInput) (hG : G.1=0) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput G.encode r k))) :
    decodeEstimate (randomProgram.run (estimateInput G.encode r k) tape)=some 1 := by
  rcases G with ⟨n,G⟩
  change n=0 at hG
  subst n
  rw [run_canonical ⟨0,G⟩ r k (by rfl)]
  simp [estimate,uniformOutput,shortOutput,shortCounts,reciprocalProductOutput]

lemma malformed_zero (raw : BitString) (h : GraphInput.decode (GraphCountSetup.graph raw)=none) :
    evaluate raw=encodeRatio 0 0 := by simp [evaluate,h]

/-- No supplied initializer, sampler, runtime, size or counting certificate
remains: this is an actual RandomBitProgram-based general graph FPRAS. -/
theorem hasFPRAS : HasFPRAS SamplerRuntime.GraphFunctional.promised GraphInput.perfectMatchingProblem :=
  ⟨randomProgram,approximationGuarantee⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
