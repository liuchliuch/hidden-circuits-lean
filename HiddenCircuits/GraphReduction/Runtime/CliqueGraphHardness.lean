import HiddenCircuits.GraphReduction.QueryRepresentations
import HiddenCircuits.GraphReduction.Runtime.MonotoneHardness
import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueWordSolver
import HiddenCircuits.Approximation.OrderedIntervals

/-! Retained graph-only operational hardness statements, structurally split
from CliqueHardness so their validation is independent of endpoint serialization. -/
namespace HiddenCircuits.GraphReduction
open Complexity
open Runtime.WordGraph

def UnitIntervalGraph {V : Type} (G : SimpleGraph V) : Prop := Nonempty (UnitInterval.Representation G)
def ChordalPermutationGraph {V : Type} (G : SimpleGraph V) : Prop :=
  Chordal G ∧ ∃D : PermutationDiagram V,D.graph=G

lemma unitGraphInput_unit {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    UnitIntervalGraph (unitGraphInput (fun i => ps.get i) S T s).2.graph := ⟨unitMatrixRepresentation ps S T s⟩
lemma privateGraphInput_chordalPermutation {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    ChordalPermutationGraph (privateGraphInput pairs S T s).2.graph :=
  ⟨privateGraphInput_chordal pairs S T s,privateMatrixDiagram pairs S T s,privateMatrixDiagram_graph pairs S T s⟩

lemma unit_wordSolverSpec (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => UnitIntervalGraph G.2.graph) g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec (CliqueDriver.program .unit) g (CliqueDriver.time .unit) := by
  intro w
  apply CliqueDriver.program_executes .unit g w
  intro _ q
  exact hg (CliqueRecovery.query false w q) (unitGraphInput_unit _ _ _ _)
lemma private_wordSolverSpec (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => ChordalPermutationGraph G.2.graph) g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec (CliqueDriver.program .privateGraph) g (CliqueDriver.time .privateGraph) := by
  intro w
  apply CliqueDriver.program_executes .privateGraph g w
  intro _ q
  exact hg (CliqueRecovery.query true w q) (privateGraphInput_chordalPermutation _ _ _ _)

theorem unit_matching_sharpPHard (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => UnitIntervalGraph G.2.graph) g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard (CliqueDriver.program .unit) g (CliqueDriver.time .unit) (unit_wordSolverSpec g hg)
theorem private_matching_sharpPHard (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => ChordalPermutationGraph G.2.graph) g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard (CliqueDriver.program .privateGraph) g (CliqueDriver.time .privateGraph) (private_wordSolverSpec g hg)
theorem unit_matching_sharpPComplete : ClassMatchingSharpPComplete (fun G => UnitIntervalGraph G.2.graph) :=
  ⟨⟨GraphInput.perfectMatchingProblem,GraphVerifier.MatchingRuntime.perfectMatching_sharpP,classMatchingOracle_full _⟩,
    unit_matching_sharpPHard⟩
theorem private_matching_sharpPComplete : ClassMatchingSharpPComplete (fun G => ChordalPermutationGraph G.2.graph) :=
  ⟨⟨GraphInput.perfectMatchingProblem,GraphVerifier.MatchingRuntime.perfectMatching_sharpP,classMatchingOracle_full _⟩,
    private_matching_sharpPHard⟩

theorem quasimonotone_matching_sharpPHard (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => Approximation.Quasimonotone G.2.graph) g) : SharpPHard g := by
  apply unit_matching_sharpPHard g
  intro G hG
  exact hg G (Approximation.UnitInterval.Representation.quasimonotone hG.some)
theorem quasimonotone_matching_sharpPComplete : ClassMatchingSharpPComplete (fun G => Approximation.Quasimonotone G.2.graph) :=
  ⟨⟨GraphInput.perfectMatchingProblem,GraphVerifier.MatchingRuntime.perfectMatching_sharpP,classMatchingOracle_full _⟩,
    quasimonotone_matching_sharpPHard⟩

end HiddenCircuits.GraphReduction
