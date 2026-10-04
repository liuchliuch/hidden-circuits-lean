import HiddenCircuits.Approximation.SelfReduction.Runtime.MapLoop
import HiddenCircuits.Approximation.SamplerRuntime.MonotoneSampler

/-! Actual repeated calls to the now-compiled monotone sampler. The supplied
sampler block is instantiated here, so no implementation premise remains. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open GraphReduction.MonotoneEndpointEncoding

noncomputable def samplerBatch : OracleBlock 48 := mapProgram SamplerRuntime.MonotoneSampler.program

/-- Every sampler call is real; parsing, output growth and list serialization
are charged, and all callback work stacks are cleaned between calls. -/
theorem samplerBatch_executes (g : BitString → ℕ) (requests : List BitString) (N : ℕ)
    (hrequests : ∀ request ∈ requests, request.length ≤ N) :
    ∃ t, samplerBatch.Executes g
      (Function.update (fun _ : Fin 49 => ([] : BitString)) 0 (encodeBitList requests))
      (Function.update (fun _ : Fin 49 => ([] : BitString)) 0
        (encodeBitList (requests.map SamplerRuntime.Functional.evaluate))) t ∧
      t ≤ 6*(encodeBitList requests).length+
        requests.length*(15*N+11*SamplerRuntime.MonotoneSampler.time.eval N+24)+11 := by
  apply mapProgram_executes _ _ g requests N (SamplerRuntime.MonotoneSampler.time.eval N) hrequests
  intro request hr
  obtain ⟨t,ht,hb⟩ := SamplerRuntime.MonotoneSampler.program_executes g request
  exact ⟨t,ht,hb.trans (polynomial_nat_eval_mono _ (hrequests request hr))⟩

/-- Concrete batch on one actual endpoint instance with a fixed unary accuracy
parameter and explicit supplied finite coin blocks. -/
theorem canonicalBatch_executes (g : BitString → ℕ) (E : Input) (T m : ℕ) (coins : List BitString)
    (hcoins : ∀ tape ∈ coins, tape.length=m) :
    let context := sampleInput (encode E) T
    let N := 2*context.length+m+1
    ∃ t, samplerBatch.Executes g
      (Function.update (fun _ : Fin 49 => ([] : BitString)) 0
        (encodeBitList (coins.map (fun tape => pairBits context tape))))
      (Function.update (fun _ : Fin 49 => ([] : BitString)) 0
        (encodeBitList (coins.map (fun tape => SamplerRuntime.Core.evaluate E.2 context.length tape)))) t ∧
      t ≤ 6*(encodeBitList (coins.map (fun tape => pairBits context tape))).length+
        coins.length*(15*N+11*SamplerRuntime.MonotoneSampler.time.eval N+24)+11 := by
  dsimp only
  have hreq : ∀ request ∈ coins.map (fun tape => pairBits (sampleInput (encode E) T) tape),
      request.length ≤ 2*(sampleInput (encode E) T).length+m+1 := by
    intro request hr
    obtain ⟨tape,ht,rfl⟩ := List.mem_map.mp hr
    simp [hcoins tape ht]
  obtain ⟨t,ht,hb⟩ := samplerBatch_executes g _ _ hreq
  refine ⟨t,?_,by simpa using hb⟩
  simpa only [List.map_map,Function.comp_def,SamplerRuntime.Functional.evaluate_canonical] using ht

 theorem samplerBatch_queryFree : samplerBatch.QueryFree :=
  mapProgram_queryFree _ SamplerRuntime.MonotoneSampler.program_queryFree

end HiddenCircuits.Approximation.SelfReduction.Runtime
