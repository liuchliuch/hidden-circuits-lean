import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordQueryBounds
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSampleNoQuery
import HiddenCircuits.GraphReduction.Runtime.DescriptorFrontNoQuery

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph
open Complexity OracleBlock
namespace PairedQuery
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (rename_queryFree _ _ DescriptorFront.program_queryFree)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ monotoneEmitter_queryFree)))
end PairedQuery
namespace WordQuery
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (rename_queryFree _ _ WordSample.program_queryFree)
  (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _))
    (rename_queryFree _ _ PairedQuery.program_queryFree))
end WordQuery
end HiddenCircuits.GraphReduction.Runtime.WordGraph
