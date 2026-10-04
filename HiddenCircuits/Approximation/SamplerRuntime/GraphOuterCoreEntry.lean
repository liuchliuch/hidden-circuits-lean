import HiddenCircuits.Approximation.SamplerRuntime.GraphOuterFront
import HiddenCircuits.Approximation.SamplerRuntime.GraphOuterCorePreparation

/-! Exact total-parser to tape-splitter boundary. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
open Complexity Complexity.OracleBlock Polynomial
open Outer (graph tape inputSize preValid unary)
set_option maxHeartbeats 2000000

lemma core_entry (raw : BitString) (G : GraphInput) (he : GraphInput.decode (graph raw)=some G) :
    afterValid raw=GraphOuterCorePreparation.entryStore (graph raw) G.2.bits G.1 (inputSize raw) (tape raw) := by
  obtain ⟨hn,hp⟩ := GraphParser.output_fields he
  funext i;fin_cases i <;> simp [afterValid,postParser,store,hn,hp,
    GraphOuterCorePreparation.entryStore,GraphOuterCorePreparation.workingStore]

lemma core_entry_bounds (raw : BitString) (G : GraphInput)
    (he : GraphInput.decode (graph raw)=some G) :
    G.1 ≤ inputSize raw ∧ G.2.bits.length≤raw.length := by
  refine ⟨(GraphInput.decode_vertices_bound he).trans (Outer.graph_length raw),?_⟩
  obtain ⟨_,hfields⟩ := GraphParser.output_fields he
  have hparse := (GraphVerifier.Runtime.parse_lengths (graph raw)).2
  change (GraphParser.output (graph raw) 2).length≤(graph raw).length at hparse
  rw [hfields] at hparse
  exact hparse.trans ((Outer.graph_length raw).trans (Outer.inputSize_le raw))

end HiddenCircuits.Approximation.SamplerRuntime.GraphOuter
