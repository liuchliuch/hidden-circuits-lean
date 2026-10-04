import HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCountProgram

/-! An actual finite fully polynomial randomized approximation scheme for the
ordinary canonical monotone endpoint encoding. All initialization, sampling,
self-reduction, concentration and bit arithmetic obligations are discharged. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCount
open Complexity GraphReduction.MonotoneEndpointEncoding

noncomputable def randomProgram : RandomBitProgram where
  evaluate := evaluate
  polynomialTime := evaluate_polyTime
  randomBits := SelfReduction.EndpointResidual.randomBitsPolynomial

@[simp] theorem randomProgram_bits (request : BitString) :
    randomProgram.bits request=SelfReduction.EndpointResidual.randomBitsPolynomial.eval request.length := rfl

 theorem run_canonical (E : Input) (r k : ℕ)
    (tape : CoinTape (randomProgram.bits (estimateInput (encode E) r k))) :
    randomProgram.run (estimateInput (encode E) r k) tape=
      endpointEstimate (estimateInput (encode E) r k).length E (CountSetup.canonical_bounds E r k).1 (List.ofFn tape) := by
  apply evaluate_canonical
  simp

/-- Exact zero on every random tape and unconditional exponentially amplified
relative accuracy for the actual encoded polynomial-time bit machine. -/
theorem approximationGuarantee : ApproximationGuarantee randomProgram SamplerRuntime.Output.promised count := by
  intro x hx r k
  obtain ⟨E,rfl⟩ := hx
  have hb := CountSetup.canonical_bounds E r k
  constructor
  · intro hz tape
    rw [run_canonical]
    exact endpointEstimate_zero _ E hb.1 (by simpa only [count_encode] using hz) _
  · simp only [randomProgram_bits]
    simp_rw [run_canonical]
    rw [count_encode]
    exact endpointEstimate_guarantee _ E hb.1 r k hb.2.1 hb.2.2

/-- No supplied sampler, initial matching, recurrence certificate, counting
oracle or polynomial-time hypothesis remains in this existence theorem. -/
theorem hasFPRAS : HasFPRAS SamplerRuntime.Output.promised count :=
  ⟨randomProgram,approximationGuarantee⟩

end HiddenCircuits.Approximation.SelfReduction.Runtime.MonotoneCount
