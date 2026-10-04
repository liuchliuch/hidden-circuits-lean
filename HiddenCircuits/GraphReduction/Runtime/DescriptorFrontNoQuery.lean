import HiddenCircuits.GraphReduction.Runtime.DescriptorFront

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity OracleBlock
namespace DescriptorRectangle
lemma loop_queryFree : loop.QueryFree := whilePop_queryFree _ _ _
  (seq_queryFree _ _ (rename_queryFree _ _ DescriptorRow.program_queryFree) (push_queryFree _ _))
  (seq_queryFree _ _ (rename_queryFree _ _ DescriptorRow.program_queryFree) (push_queryFree _ _))
end DescriptorRectangle
namespace DescriptorFront
lemma maskRow_queryFree : maskRow.QueryFree := rename_queryFree _ _ DescriptorMaskRow.program_queryFree
lemma row_queryFree : row.QueryFree := rename_queryFree _ _ DescriptorRow.program_queryFree
lemma rectangle_queryFree (probe : Bool) : (rectangle probe).QueryFree := rename_queryFree _ _ DescriptorRectangle.program_queryFree
lemma rectangleLoop_queryFree (probe : Bool) : (rectangleLoop probe).QueryFree := rename_queryFree _ _ DescriptorRectangle.loop_queryFree
lemma difference_queryFree : difference.QueryFree := rename_queryFree _ _ DescriptorMaskDifference.program_queryFree
lemma retag_queryFree (side probe : Bool) : (retag side probe).QueryFree := seq_queryFree _ _ (clear_queryFree _) (prepend_queryFree _ _)
lemma probes_queryFree (side : Bool) : (probes side).QueryFree := seq_queryFree _ _ (retag_queryFree _ _)
  (seq_queryFree _ _ (rectangle_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (retag_queryFree _ _)))
end DescriptorFront
namespace DescriptorEven
lemma sourceRow_queryFree : sourceRow.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) DescriptorFront.maskRow_queryFree
lemma differenceRow_queryFree (target : Bool) : (differenceRow target).QueryFree := by
  cases target <;> exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ DescriptorFront.difference_queryFree DescriptorFront.maskRow_queryFree))
lemma positive_queryFree : positive.QueryFree := seq_queryFree _ _ sourceRow_queryFree
  (seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (DescriptorFront.rectangleLoop_queryFree _)
    (seq_queryFree _ _ (differenceRow_queryFree _) (clear_queryFree _))))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (branchPop_queryFree _ _ _ _ (differenceRow_queryFree _) positive_queryFree positive_queryFree)
end DescriptorEven
namespace DescriptorOdd
lemma parse_queryFree : parse.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (Circuit.Runtime.SamplePairParser.on_queryFree _) (rename_queryFree _ _ DescriptorOddParse.program_queryFree))
lemma restore_queryFree : restore.QueryFree := seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (prepend_queryFree _ _))
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ parse_queryFree
  (seq_queryFree _ _ DescriptorFront.row_queryFree (seq_queryFree _ _ restore_queryFree (push_queryFree _ _)))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (whilePop_queryFree _ _ _ body_queryFree body_queryFree) (clear_queryFree _)
end DescriptorOdd
namespace DescriptorFront
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (prepend_queryFree _ _)
  (seq_queryFree _ _ (seq_queryFree _ _ DescriptorEven.program_queryFree
    (seq_queryFree _ _ (probes_queryFree _) (seq_queryFree _ _ DescriptorOdd.program_queryFree (probes_queryFree _))))
    (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))
end DescriptorFront
end HiddenCircuits.GraphReduction.Runtime
