import HiddenCircuits.Approximation.SamplerRuntime.CoordinateSamplerRuntime

/-! Unconditional machine-grounded FPAUS for coordinate-only equal-length
interval inputs. Labels, coincident intervals, failure mass and empty solution
sets are retained. The randomness bound is polynomial in the coordinate request,
not in an externally supplied or separately charged adjacency matrix. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.CoordinateSampler
open Complexity GraphReduction Polynomial FiniteChains
attribute [local instance] Classical.propDecidable

/-- Canonical coordinate representations with a positive common denominator. -/
def promised (xs : BitString) : Prop :=
  ∃(G : GraphInput) (R : UnitIntegerRepresentation G),unitCoordinateBits G R=xs

/-- The graph compiler preserves all original vertex labels. The same partner
array bytes therefore encode the matching of the represented intervals. -/
noncomputable def solutions (xs : BitString) : Finset BitString :=
  GraphFunctional.solutions (Runtime.CoordinateGraph.bits xs)

@[simp] lemma solutions_canonical (G : GraphInput) (R : UnitIntegerRepresentation G) :
    solutions (unitCoordinateBits G R)=PartnerOutput.witnesses G.2 := by
  simp only [solutions,Runtime.CoordinateGraph.bits_representation,GraphFunctional.solutions_encode]

/-- The sampler target has exactly the coordinate-input counting extension's
cardinality, including on the explicit total malformed-input extension. -/
lemma solutions_count (xs : BitString) : (solutions xs).card=unitCoordinateProblem xs := by
  change (PartnerOutput.solutions (Runtime.CoordinateGraph.bits xs)).card=
    GraphInput.perfectMatchingProblem (Runtime.CoordinateGraph.bits xs)
  exact PartnerOutput.count_solutions _

lemma solutions_canonical_count (G : GraphInput) (R : UnitIntegerRepresentation G) :
    (solutions (unitCoordinateBits G R)).card=perfectMatchingCount G.2.graph := by
  rw [solutions_count]
  exact unitCoordinateProblem_oracle G R

/-- Rational interval semantics supplied by integer numerators and denominator. -/
def representation (G : GraphInput) (R : UnitIntegerRepresentation G) : UnitInterval.Representation G.2.graph where
  length := 1
  positive := by norm_num
  left i := (R.left i:ℚ)/R.denominator
  adjacency := R.adjacency

lemma quasimonotone (G : GraphInput) (R : UnitIntegerRepresentation G) : Quasimonotone G.2.graph :=
  UnitInterval.Representation.quasimonotone (representation G R)

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
    3*((sampleInput (Runtime.CoordinateGraph.bits xs) k).length+1)^4+
      PartnerBudget.bits ((sampleInput (Runtime.CoordinateGraph.bits xs) k).length+1)≤
      randomProgram.bits (sampleInput xs k) := by
  have hh := polynomial_nat_eval_mono GraphFunctional.bitsPolynomial (request_size (sampleInput xs k))
  dsimp only at hh
  rw [bits_eq]
  simpa only [request_canonical,GraphFunctional.bits_eval] using hh

lemma canonical_bits_dominate (G : GraphInput) (R : UnitIntegerRepresentation G) (k : ℕ) :
    3*((sampleInput G.encode k).length+1)^4+PartnerBudget.bits ((sampleInput G.encode k).length+1)≤
      randomProgram.bits (sampleInput (unitCoordinateBits G R) k) := by
  simpa only [Runtime.CoordinateGraph.bits_representation] using bits_dominate (unitCoordinateBits G R) k

lemma run_canonical (G : GraphInput) (R : UnitIntegerRepresentation G) (k : ℕ)
    (r : CoinTape (randomProgram.bits (sampleInput (unitCoordinateBits G R) k))) :
    randomProgram.run (sampleInput (unitCoordinateBits G R) k) r=
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
theorem zero_count (G : GraphInput) (R : UnitIntegerRepresentation G)
    (hzero : perfectMatchingCount G.2.graph=0) (k : ℕ)
    (r : CoinTape (randomProgram.bits (sampleInput (unitCoordinateBits G R) k))) :
    decodeSample (randomProgram.run (sampleInput (unitCoordinateBits G R) k) r)=none := by
  apply (samplingGuarantee _ ⟨G,R,rfl⟩ k).2.1
  apply Finset.card_eq_zero.mp
  rw [solutions_canonical_count,hzero]

/-- Corollary 1.3 sampling on the interval-coordinate input itself, with no
supplied initializer, adjacency matrix, runtime premise, or positivity promise. -/
theorem hasFPAUS : HasFPAUS promised solutions := ⟨randomProgram,samplingGuarantee⟩

end HiddenCircuits.Approximation.SamplerRuntime.CoordinateSampler
