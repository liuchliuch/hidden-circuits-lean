/- New wrapper, October2026, instantiated from the checked literal strict graph compiler. -/
import HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerSamplerRuntime
import HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerGeometry
import HiddenCircuits.Approximation.SamplerRuntime.GraphZeroVertices

/-! Unconditional machine-grounded FPAUS for strict-radius integer
interval inputs. Labels, coincident intervals, failure mass and empty solution
sets are retained. The randomness bound is polynomial in the coordinate request,
not in an externally supplied or separately charged adjacency matrix. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerSampler
open Complexity GraphReduction Polynomial FiniteChains
attribute [local instance] Classical.propDecidable

/-- Canonical labelled integer coordinates with a positive strict radius. -/
def promised (xs : BitString) : Prop :=
  ∃(G : GraphInput) (R : StrictIntegerRepresentation G),strictIntegerBits G R=xs

/-- The graph compiler preserves all original vertex labels. The same partner
array bytes therefore encode the matching of the represented intervals. -/
noncomputable def solutions (xs : BitString) : Finset BitString :=
  GraphFunctional.solutions (Runtime.StrictInteger.bits xs)

@[simp] lemma solutions_canonical (G : GraphInput) (R : StrictIntegerRepresentation G) :
    solutions (strictIntegerBits G R)=PartnerOutput.witnesses G.2 := by
  simp only [solutions,Runtime.StrictInteger.bits_representation,GraphFunctional.solutions_encode]

/-- The sampler target has exactly the coordinate-input counting extension's
cardinality, including on the explicit total malformed-input extension. -/
lemma solutions_count (xs : BitString) : (solutions xs).card=strictIntegerProblem xs := by
  change (PartnerOutput.solutions (Runtime.StrictInteger.bits xs)).card=
    GraphInput.perfectMatchingProblem (Runtime.StrictInteger.bits xs)
  exact PartnerOutput.count_solutions _

lemma solutions_canonical_count (G : GraphInput) (R : StrictIntegerRepresentation G) :
    (solutions (strictIntegerBits G R)).card=perfectMatchingCount G.2.graph := by
  rw [solutions_count]
  exact strictIntegerProblem_oracle G R

/-- Positive integer radius is the paper promise; count positivity is not required. -/
lemma quasimonotone (G : GraphInput) (R : StrictIntegerRepresentation G) : Quasimonotone G.2.graph :=
  StrictIntegerGeometry.quasimonotone G R

noncomputable def bitsPolynomial : Polynomial ℕ := GraphFunctional.bitsPolynomial.comp requestSize
noncomputable def randomProgram : RandomBitProgram where
  evaluate := evaluate
  polynomialTime := evaluate_polyTime
  randomBits := bitsPolynomial

/-- The fair tape is allocated from the original coordinate request size. -/
lemma bits_eq (input : BitString) : randomProgram.bits input=
    GraphFunctional.bitsPolynomial.eval (requestSize.eval input.length) := by
  simp only [randomProgram,RandomBitProgram.bits,bitsPolynomial,eval_comp]

/-- Polynomial allocation dominates the expanded graph request's actual budget. -/
lemma bits_dominate (xs : BitString) (k : ℕ) :
    3*((sampleInput (Runtime.StrictInteger.bits xs) k).length+1)^4+
      PartnerBudget.bits ((sampleInput (Runtime.StrictInteger.bits xs) k).length+1)≤
      randomProgram.bits (sampleInput xs k) := by
  have hh := polynomial_nat_eval_mono GraphFunctional.bitsPolynomial (request_size (sampleInput xs k))
  dsimp only at hh
  rw [bits_eq]
  simpa only [request_canonical,GraphFunctional.bits_eval] using hh

lemma canonical_bits_dominate (G : GraphInput) (R : StrictIntegerRepresentation G) (k : ℕ) :
    3*((sampleInput G.encode k).length+1)^4+PartnerBudget.bits ((sampleInput G.encode k).length+1)≤
      randomProgram.bits (sampleInput (strictIntegerBits G R) k) := by
  simpa only [Runtime.StrictInteger.bits_representation] using bits_dominate (strictIntegerBits G R) k

lemma run_canonical (G : GraphInput) (R : StrictIntegerRepresentation G) (k : ℕ)
    (r : CoinTape (randomProgram.bits (sampleInput (strictIntegerBits G R) k))) :
    randomProgram.run (sampleInput (strictIntegerBits G R) k) r=
      GraphFunctional.core G.2 ((sampleInput G.encode k).length+1) (List.ofFn r) :=
  evaluate_canonical G R k _

/-- Total variation is controlled on the actual unconditioned distribution of
finite machine outputs, including failed initialization and zero counts. -/
theorem samplingGuarantee : SamplingGuarantee randomProgram promised solutions := by
  intro xs hx k
  obtain ⟨G,R,rfl⟩ := hx
  refine ⟨?_,?_,?_⟩
  · intro r w hw
    rw [run_canonical] at hw
    rw [solutions_canonical]
    exact GraphFunctional.core_sound G.2 _ _ w hw
  · intro he r
    rw [solutions_canonical] at he
    rw [run_canonical]
    exact GraphFunctional.core_empty G.2 _ _ he
  · intro A
    simp only [run_canonical,solutions_canonical]
    exact GraphPadding.core_event_error G.2 (quasimonotone G R) _ k _
      (GraphPadding.size_bounds G k).1 (GraphPadding.size_bounds G k).2 (canonical_bits_dominate G R k) A

/-- Exact zero-count semantics on every canonical coordinate representation. -/
theorem zero_count (G : GraphInput) (R : StrictIntegerRepresentation G)
    (hzero : perfectMatchingCount G.2.graph=0) (k : ℕ)
    (r : CoinTape (randomProgram.bits (sampleInput (strictIntegerBits G R) k))) :
    decodeSample (randomProgram.run (sampleInput (strictIntegerBits G R) k) r)=none := by
  apply (samplingGuarantee _ ⟨G,R,rfl⟩ k).2.1
  apply Finset.card_eq_zero.mp
  rw [solutions_canonical_count,hzero]

/-- Sampling on the literal strict integer-radius input itself, with no
supplied initializer, adjacency matrix, runtime premise, or positive-count promise. -/
theorem hasFPAUS : HasFPAUS promised solutions := ⟨randomProgram,samplingGuarantee⟩

@[simp] lemma solutions_raw (xs : BitString) :
    solutions xs=PartnerOutput.witnesses (GraphReduction.Runtime.StrictInteger.graphInput xs).2 := by
  simp only [solutions,GraphReduction.Runtime.StrictInteger.bits_graph,GraphFunctional.solutions_encode]

/-- The zero-radius and malformed nonempty extensions really fail on every tape. -/
theorem zero_count_raw (xs : BitString) (hz:strictIntegerProblem xs=0) (k : ℕ)
    (tape : CoinTape (randomProgram.bits (sampleInput xs k))) :
    decodeSample (randomProgram.run (sampleInput xs k) tape)=none := by
  change decodeSample (evaluate (pairBits (sampleInput xs k) (List.ofFn tape)))=none
  rw [evaluate_raw]
  apply GraphPadding.evaluate_empty
  rw [GraphFunctional.solutions_encode,←solutions_raw]
  exact Finset.card_eq_zero.mp ((solutions_count xs).trans hz)

theorem nonpositive_nonempty (xs : BitString) (hr:GraphReduction.Runtime.StrictInteger.radius xs≤0)
    (hn:0<(LooseWordList.words (GraphReduction.Runtime.StrictInteger.data xs)).length) (k : ℕ)
    (tape : CoinTape (randomProgram.bits (sampleInput xs k))) :
    decodeSample (randomProgram.run (sampleInput xs k) tape)=none :=
  zero_count_raw xs (strictIntegerProblem_nonpositive_nonempty xs hr hn) k tape

/-- A decoded empty list returns the successful empty witness, even at radius0. -/
theorem empty_raw (xs : BitString) (hn:(LooseWordList.words (GraphReduction.Runtime.StrictInteger.data xs)).length=0)
    (k : ℕ) (tape : CoinTape (randomProgram.bits (sampleInput xs k))) :
    randomProgram.run (sampleInput xs k) tape=[true] := by
  change evaluate (pairBits (sampleInput xs k) (List.ofFn tape))=[true]
  rw [evaluate_raw]
  exact GraphFunctional.evaluate_zero_vertices (GraphReduction.Runtime.StrictInteger.graphInput xs) hn k _
lemma empty_solutions_count (xs : BitString)
    (hn:(LooseWordList.words (GraphReduction.Runtime.StrictInteger.data xs)).length=0) :
    (solutions xs).card=1 := by rw [solutions_count];exact StrictIntegerGeometry.raw_empty_count xs hn

end HiddenCircuits.Approximation.SamplerRuntime.StrictIntegerSampler
