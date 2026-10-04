import HiddenCircuits.Circuit.Runtime.SourceHardness
import HiddenCircuits.GraphReduction.Runtime.WordGraph.PrivateBothWordSolver

/-! Exact source hardness when both interval and permutation representations are
physically supplied with every ordinary binary adjacency-matrix graph. -/
namespace HiddenCircuits.GraphReduction
open Complexity Runtime.WordGraph

lemma suppliedBoth_wordSolverSpec (g : BitString → ℕ) (hg : SuppliedIntervalPermutationOracle g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec PrivateBothDriver.program g PrivateBothDriver.time := by
  intro w
  apply PrivateBothDriver.program_executes g w
  intro _ q
  change g (Runtime.PrivateBothQuery.bits (fun i => (sampleWord w.word q.1.val).get i)
    w.source w.target (2*q.2.val)) = _
  rw [Runtime.PrivateBothQuery.bits_correct]
  exact hg (CliqueRecovery.query true w q)
    (privateMatrixDiagram (fun i => (sampleWord w.word q.1.val).get i) w.source w.target (2*q.2.val))
    (privateMatrixIntervalRepresentation (fun i => (sampleWord w.word q.1.val).get i) w.source w.target (2*q.2.val))
    (privateMatrixDiagram_graph _ _ _ _)

/-- No recognition certificate or unexecuted representation constructor is an input. -/
theorem suppliedBoth_matching_sharpPHard (g : BitString → ℕ) (hg : SuppliedIntervalPermutationOracle g) :
    SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard PrivateBothDriver.program g PrivateBothDriver.time
    (suppliedBoth_wordSolverSpec g hg)

end HiddenCircuits.GraphReduction
