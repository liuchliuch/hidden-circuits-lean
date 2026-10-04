import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotoneEndpointWordSolver
import HiddenCircuits.GraphReduction.Runtime.EndpointMembership
import HiddenCircuits.Circuit.Runtime.SourceHardness

/-! Native endpoint-form #P completeness. The reduction physically generates
canonical a/b endpoint arrays. The total count rejects malformed inputs, and
membership uses the independently checked all-raw endpoint-to-graph compiler. -/
namespace HiddenCircuits.GraphReduction
open Complexity Runtime Runtime.WordGraph

noncomputable def endpointQuery (w : WordInstance) (hw : w.word≠[]) (t s : ℕ) : MonotoneEndpointEncoding.Input :=
  ⟨MonotoneEndpointRuntime.leftCard w.particles (sampleWord w.word t).length s w.source w.target,
    monotoneQueryEndpoints (List.length_pos_iff.mpr (pairedQuery_nonempty w.word hw t))
      (fun i=>(sampleWord w.word t).get i) w.source w.target s⟩
lemma endpointQuery_bits (w : WordInstance) (hw : w.word≠[]) (t s : ℕ) :
    MonotoneEndpointAnswer.queryBits w t s=MonotoneEndpointEncoding.encode (endpointQuery w hw t s) :=
  MonotoneEndpointRuntime.bits_correct (List.length_pos_iff.mpr (pairedQuery_nonempty w.word hw t))
    (fun i=>(sampleWord w.word t).get i) w.source w.target
lemma endpointQuery_count (w : WordInstance) (hw : w.word≠[]) (t s : ℕ) :
    perfectMatchingCount (MonotoneEndpointWordQuery.graphInput w t s).2.graph=
      Fintype.card (endpointQuery w hw t s).2.Permutations :=
  monotoneQueryEndpoints_count (List.length_pos_iff.mpr (pairedQuery_nonempty w.word hw t))
    (fun i=>(sampleWord w.word t).get i) w.source w.target s

def MonotoneEndpointOracle (g : BitString → ℕ) : Prop :=
  ∀E : MonotoneEndpointEncoding.Input,g (MonotoneEndpointEncoding.encode E)=Fintype.card E.2.Permutations
lemma monotoneEndpoint_count_oracle : MonotoneEndpointOracle MonotoneEndpointEncoding.count := by
  intro E;exact MonotoneEndpointEncoding.count_encode E

lemma monotoneEndpoint_wordSolverSpec (g : BitString → ℕ) (hg : MonotoneEndpointOracle g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec MonotoneEndpointDriver.program g MonotoneEndpointDriver.time := by
  intro w
  apply MonotoneEndpointDriver.program_executes g w
  intro hw q
  change g (MonotoneEndpointAnswer.queryBits w q.1.val q.2.val)=_
  rw [endpointQuery_bits w hw,hg]
  exact (endpointQuery_count w hw q.1.val q.2.val).symm

theorem monotoneEndpoint_counting_sharpPHard (g : BitString → ℕ) (hg : MonotoneEndpointOracle g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard MonotoneEndpointDriver.program g MonotoneEndpointDriver.time
    (monotoneEndpoint_wordSolverSpec g hg)
theorem monotoneEndpoint_count_sharpPHard : SharpPHard MonotoneEndpointEncoding.count :=
  monotoneEndpoint_counting_sharpPHard MonotoneEndpointEncoding.count monotoneEndpoint_count_oracle

/-- Full native-input completeness, with total all-raw #P membership and an
actual polynomial finite-stack oracle reduction from the original source. -/
theorem monotoneEndpoint_sharpP_complete :
    SharpP MonotoneEndpointEncoding.count ∧ SharpPHard MonotoneEndpointEncoding.count ∧
      MonotoneEndpointOracle MonotoneEndpointEncoding.count :=
  ⟨monotoneEndpoint_count_sharpP,monotoneEndpoint_count_sharpPHard,monotoneEndpoint_count_oracle⟩
end HiddenCircuits.GraphReduction
