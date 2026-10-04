import HiddenCircuits.Approximation.SamplerRuntime.GraphSampler

/-! Exact empty-vertex behavior of the actual graph sampler, on every raw tape. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphFunctional
open Complexity Initialization.RawExtraction

lemma core_zero_vertices (G : MatrixGraph 0) (N : ℕ) (coins : BitString) : core G N coins=[true] := by
  have hp (source : BitString) : initialPermutation G N source=some (Equiv.refl (Fin 0)) := by
    have hu : (Finset.univ : Finset (Fin 0))=∅ := by ext i;exact Fin.elim0 i
    simp [initialPermutation,hu]
  have hn (source : BitString) : initialPartner G N source≠none := by
    intro h
    have h0:=(initialPartner_none_iff G N source).mp h
    rw [hp] at h0
    cases h0
  obtain ⟨P,hP⟩:=Option.ne_none_iff_exists'.mp (hn (TapeRead.takePadded (3*N^4) coins))
  simp [core,hP,PartnerRunner.afterInitialize,PartnerRunner.evaluate,PartnerOutput.success,
    PartnerOutput.witness,PartnerMove.witness,Output.witness,Switch.rowWords,GraphReduction.MonotoneEndpointEncoding.rows,
    encodeBitList]

lemma evaluate_zero_vertices (G : GraphInput) (hG:G.1=0) (k : ℕ) (coins : BitString) :
    evaluate (pairBits (sampleInput G.encode k) coins)=[true] := by
  rcases G with ⟨n,G⟩
  change n=0 at hG
  subst n
  rw [evaluate_canonical,core_zero_vertices]
end HiddenCircuits.Approximation.SamplerRuntime.GraphFunctional
