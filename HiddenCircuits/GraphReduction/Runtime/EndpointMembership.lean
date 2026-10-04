import HiddenCircuits.GraphReduction.Runtime.EndpointGraphProgram
import HiddenCircuits.Complexity.GraphVerifier.MatchingPullback

/-! Native endpoint counting belongs to #P on all raw strings, via an actual
query-free polynomial endpoint-parser/adjacency compiler and matching verifier. -/
namespace HiddenCircuits.GraphReduction
open Complexity

theorem monotoneEndpoint_count_sharpP : SharpP MonotoneEndpointEncoding.count := by
  have h := GraphVerifier.MatchingPullback.sharpP_of_graph_compiler
    Runtime.EndpointGraph.program Runtime.EndpointGraph.program_queryFree Runtime.EndpointGraph.compiledBits
    Runtime.EndpointGraph.time Runtime.EndpointGraph.size (by
      intro xs
      obtain ⟨c,hc,hb⟩ := Runtime.EndpointGraph.program_executes (fun _=>0) xs
      exact ⟨_,c,hc,Function.update_self _ _ _,hb⟩) (by
      intro xs
      simpa [Runtime.EndpointGraph.size] using Runtime.EndpointGraph.compiled_size xs)
  have he : MonotoneEndpointEncoding.count=GraphInput.perfectMatchingProblem ∘ Runtime.EndpointGraph.compiledBits := by
    funext xs;exact Runtime.EndpointGraph.count_eq_compiled xs
  rw [he]
  exact h
end HiddenCircuits.GraphReduction
