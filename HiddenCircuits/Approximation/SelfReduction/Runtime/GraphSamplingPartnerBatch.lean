import HiddenCircuits.Approximation.SelfReduction.Runtime.FirstPartnerTotal
import HiddenCircuits.Approximation.SelfReduction.Runtime.SamplerBatch
import HiddenCircuits.Approximation.SamplerRuntime.GraphSampler

/-! The concrete initialized sampler followed by literal first-partner decoding.
Every malformed input is still a bounded clean finite computation. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def partnerDecodePorts : Fin 4 ↪ Fin 78 where
  toFun i := i.castAdd 74
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 78 => x.val) h)

noncomputable def partnerSampler : OracleBlock 77 :=
  seq SamplerRuntime.GraphSampler.program (rename firstPartnerWord partnerDecodePorts)

noncomputable def partnerEvaluate (raw : BitString) : BitString := firstPartnerValue (SamplerRuntime.GraphFunctional.evaluate raw)

noncomputable def partnerTime : Polynomial ℕ := 21*SamplerRuntime.GraphSampler.time+20*Polynomial.X+36

 theorem partnerSampler_executes (g : BitString → ℕ) (raw : BitString) :
    ∃ t, partnerSampler.Executes g (Function.update (fun _ => []) 0 raw)
      (Function.update (fun _ => []) 0 (partnerEvaluate raw)) t ∧ t ≤ partnerTime.eval raw.length := by
  obtain ⟨ts,hs,hbs⟩ := SamplerRuntime.GraphSampler.program_executes g raw
  obtain ⟨td,hd,hbd⟩ := firstPartnerWord_clean g (SamplerRuntime.GraphFunctional.evaluate raw)
  have hh : (rename firstPartnerWord partnerDecodePorts).Executes g
      (Function.update (fun _ : Fin 78 => []) 0 (SamplerRuntime.GraphFunctional.evaluate raw))
      (Function.update (fun _ : Fin 78 => []) 0 (partnerEvaluate raw)) td := by
    apply rename_executes_to firstPartnerWord partnerDecodePorts g hd
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · intro j hj
      have hj0 : j≠0 := by intro h; subst j; exact hj 0 rfl
      simp [Function.update_of_ne hj0]
  have hlen := cleanCall_output_length _ g _ _ _ hs
  refine ⟨ts+td+2,seq_executes _ _ g hs hh,?_⟩
  simp only [partnerTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

 theorem partnerSampler_queryFree : partnerSampler.QueryFree :=
  seq_queryFree _ _ SamplerRuntime.GraphSampler.program_queryFree
    (rename_queryFree _ _ firstPartnerWord_queryFree)

noncomputable def partnerBatch : OracleBlock 81 := mapProgram partnerSampler

 theorem partnerBatch_executes (g : BitString → ℕ) (requests : List BitString) (N : ℕ)
    (hrequests : ∀ request ∈ requests, request.length ≤ N) :
    ∃ t, partnerBatch.Executes g
      (Function.update (fun _ : Fin 82 => []) 0 (encodeBitList requests))
      (Function.update (fun _ : Fin 82 => []) 0 (encodeBitList (requests.map partnerEvaluate))) t ∧
      t ≤ 6*(encodeBitList requests).length+requests.length*(15*N+11*partnerTime.eval N+24)+11 := by
  apply mapProgram_executes _ _ g requests N (partnerTime.eval N) hrequests
  intro request hr
  obtain ⟨t,ht,hb⟩ := partnerSampler_executes g request
  exact ⟨t,ht,hb.trans (polynomial_nat_eval_mono _ (hrequests request hr))⟩

 theorem partnerBatch_queryFree : partnerBatch.QueryFree := mapProgram_queryFree _ partnerSampler_queryFree

/-- The general graph runner uses the very same marked unary partner codec. -/
theorem graphFirstPartner {n : ℕ} (G : MatrixGraph (n+1)) (P : PerfectPartner G.graph) :
    firstPartnerValue (SamplerRuntime.PartnerOutput.success G P)=
      true::List.replicate (P.val 0).val true := by
  exact firstPartnerValue_witness (SamplerRuntime.PartnerMove.partnerPermutation G P)

theorem graphFirstPartner_length {n : ℕ} (G : MatrixGraph n) (P : PerfectPartner G.graph) :
    (firstPartnerValue (SamplerRuntime.PartnerOutput.success G P)).length ≤ n := by
  cases n with
  | zero =>
    simp [SamplerRuntime.PartnerOutput.success,SamplerRuntime.PartnerOutput.witness,
      SamplerRuntime.PartnerMove.witness,SamplerRuntime.Output.witness,SamplerRuntime.Switch.rowWords,
      GraphReduction.MonotoneEndpointEncoding.rows,encodeBitList,firstPartnerValue]
  | succ n =>
    rw [graphFirstPartner]
    simp only [List.length_cons,List.length_replicate]
    exact (P.val 0).isLt

/-- Canonical inputs need no supplied output-size hypothesis. -/
theorem partnerEvaluate_canonical_length (G : GraphInput) (k : ℕ) (tape : BitString) :
    (partnerEvaluate (pairBits (sampleInput G.encode k) tape)).length ≤ G.1 := by
  unfold partnerEvaluate
  rw [SamplerRuntime.GraphFunctional.evaluate_canonical]
  unfold SamplerRuntime.GraphFunctional.core
  generalize Initialization.RawExtraction.initialPartner G.2 ((sampleInput G.encode k).length+1)
    (SamplerRuntime.TapeRead.takePadded (3*((sampleInput G.encode k).length+1)^4) tape) = start
  cases start with
  | none => simp [SamplerRuntime.PartnerRunner.afterInitialize]
  | some P =>
    exact graphFirstPartner_length G.2
      (SamplerRuntime.PartnerIteration.iterate G.2
        (SamplerRuntime.PartnerBudget.steps ((sampleInput G.encode k).length+1)) P
        (tape.drop (3*((sampleInput G.encode k).length+1)^4)))

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphSampling
