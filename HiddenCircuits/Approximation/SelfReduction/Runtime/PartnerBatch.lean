import HiddenCircuits.Approximation.SelfReduction.Runtime.FirstPartnerTotal
import HiddenCircuits.Approximation.SelfReduction.Runtime.SamplerBatch

/-! The concrete initialized sampler followed by literal first-partner decoding.
Every malformed input is still a bounded clean finite computation. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def partnerDecodePorts : Fin 4 ↪ Fin 45 where
  toFun i := i.castAdd 41
  inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 45 => x.val) h)

noncomputable def partnerSampler : OracleBlock 44 :=
  seq SamplerRuntime.MonotoneSampler.program (rename firstPartnerWord partnerDecodePorts)

def partnerEvaluate (raw : BitString) : BitString := firstPartnerValue (SamplerRuntime.Functional.evaluate raw)

noncomputable def partnerTime : Polynomial ℕ := 21*SamplerRuntime.MonotoneSampler.time+20*Polynomial.X+36

 theorem partnerSampler_executes (g : BitString → ℕ) (raw : BitString) :
    ∃ t, partnerSampler.Executes g (Function.update (fun _ => []) 0 raw)
      (Function.update (fun _ => []) 0 (partnerEvaluate raw)) t ∧ t ≤ partnerTime.eval raw.length := by
  obtain ⟨ts,hs,hbs⟩ := SamplerRuntime.MonotoneSampler.program_executes g raw
  obtain ⟨td,hd,hbd⟩ := firstPartnerWord_clean g (SamplerRuntime.Functional.evaluate raw)
  have hh : (rename firstPartnerWord partnerDecodePorts).Executes g
      (Function.update (fun _ : Fin 45 => []) 0 (SamplerRuntime.Functional.evaluate raw))
      (Function.update (fun _ : Fin 45 => []) 0 (partnerEvaluate raw)) td := by
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
  seq_queryFree _ _ SamplerRuntime.MonotoneSampler.program_queryFree
    (rename_queryFree _ _ firstPartnerWord_queryFree)

noncomputable def partnerBatch : OracleBlock 48 := mapProgram partnerSampler

 theorem partnerBatch_executes (g : BitString → ℕ) (requests : List BitString) (N : ℕ)
    (hrequests : ∀ request ∈ requests, request.length ≤ N) :
    ∃ t, partnerBatch.Executes g
      (Function.update (fun _ : Fin 49 => []) 0 (encodeBitList requests))
      (Function.update (fun _ : Fin 49 => []) 0 (encodeBitList (requests.map partnerEvaluate))) t ∧
      t ≤ 6*(encodeBitList requests).length+requests.length*(15*N+11*partnerTime.eval N+24)+11 := by
  apply mapProgram_executes _ _ g requests N (partnerTime.eval N) hrequests
  intro request hr
  obtain ⟨t,ht,hb⟩ := partnerSampler_executes g request
  exact ⟨t,ht,hb.trans (polynomial_nat_eval_mono _ (hrequests request hr))⟩

 theorem partnerBatch_queryFree : partnerBatch.QueryFree := mapProgram_queryFree _ partnerSampler_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime
