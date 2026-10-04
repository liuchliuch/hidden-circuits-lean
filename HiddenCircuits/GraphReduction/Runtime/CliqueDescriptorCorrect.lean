import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptor

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity
set_option maxHeartbeats 1000000

 theorem unitRecordAdj_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : UnitQueryVertex p h s S T) :
    cliqueRecordAdj false (unitVertexRecord pairs x) (unitVertexRecord pairs y)=decide ((unitIntervalQueryGraph pairs S T s).Adj x y) := by
  rcases x with (x|x)|x <;> rcases y with (y|y)|y
  all_goals simp only [unitVertexRecord,cliqueRecordAdj,cliqueDirectedRecordAdj,cliqueLocalAdj,
    unitIntervalQueryGraph,cliqueProbeGraph,unitIntervalOriginalGraph,unitIntervalAttachment]
  all_goals simp [unitIntervalCrossRelation,cutBit_first,cutBit_second,Fin.ext_iff,eq_comm,Bool.and_assoc]

 theorem privateRecordAdj_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : PrivateQueryVertex p h s S T) :
    cliqueRecordAdj true (privateVertexRecord pairs x) (privateVertexRecord pairs y)=decide ((PrivateProbe.retainedQueryGraph pairs S T s).Adj x y) := by
  rcases x with (x|x)|(⟨x|x,q⟩) <;> rcases y with (y|y)|(⟨y|y,r⟩)
  all_goals simp only [privateVertexRecord,cliqueRecordAdj,cliqueDirectedRecordAdj,cliqueLocalAdj,
    PrivateProbe.retainedQueryGraph,cliqueProbeGraph,PrivateProbe.retainedCliqueGraph,SimpleGraph.comap_adj,
    PrivateProbe.originalEmbedding,PrivateProbe.cliqueGraph,PrivateProbe.retainedLayer,PrivateProbe.layerTag]
  all_goals simp [targetRelation,cutBit_first,cutBit_second,Fin.ext_iff,eq_comm,Bool.and_assoc]
end HiddenCircuits.GraphReduction.Runtime
