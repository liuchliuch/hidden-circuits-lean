import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph
open Complexity OracleBlock BinaryArithmetic
namespace SampleAtom
lemma emit_queryFree (tag : BitString) : (emit tag).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (prepend_queryFree _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ wordEmit_queryFree) (push_queryFree _ _)))
lemma background_queryFree : background.QueryFree := seq_queryFree _ _ (prepend_queryFree _ _) (push_queryFree _ _)
lemma backgrounds_queryFree : backgrounds.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (whilePop_queryFree _ _ _ background_queryFree background_queryFree)
lemma body_queryFree (right : Bool) (tag : BitString) : (body right tag).QueryFree := by
  cases right
  · exact seq_queryFree _ _ (emit_queryFree _) (seq_queryFree _ _ backgrounds_queryFree (clear_queryFree _))
  · exact seq_queryFree _ _ backgrounds_queryFree (seq_queryFree _ _ (emit_queryFree _) (clear_queryFree _))
lemma program_queryFree : program.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree
  (branchPop_queryFree _ _ _ _ skip_queryFree (body_queryFree _ _) (body_queryFree _ _))
  (branchPop_queryFree _ _ _ _ skip_queryFree (body_queryFree _ _) (body_queryFree _ _))
end SampleAtom
namespace WordSample
lemma body_queryFree : body.QueryFree := seq_queryFree _ _
  (seq_queryFree _ _ (Circuit.Runtime.SamplePairParser.on_queryFree _) (Circuit.Runtime.SamplePairParser.on_queryFree _))
  (rename_queryFree _ _ SampleAtom.program_queryFree)
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ WordParser.program_queryFree
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (whilePop_queryFree _ _ _ body_queryFree body_queryFree) (reverseOn_queryFree _ _ _)))
end WordSample
end HiddenCircuits.GraphReduction.Runtime.WordGraph
