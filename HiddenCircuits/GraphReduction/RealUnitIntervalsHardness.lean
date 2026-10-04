import HiddenCircuits.GraphReduction.Runtime.CliqueGraphHardness
import HiddenCircuits.Approximation.RealOrderedIntervals

/-!
# Ordinary graph-input #P completeness for real unit-interval graphs

The promised class is the natural closed-real-interval class, not the family of
reduction queries and not a class with a supplied representation. The input and
oracle query are just the existing canonical finite adjacency-matrix encoding.
Membership is a total #P extension by ordinary graph perfect-matching counting.
Hardness uses the existing concrete finite polynomial-bit-time clique driver;
its rational query representations are cast to real ones without changing the
graph bytes. No recognizer, real-coordinate encoding, rationalization theorem,
or additional runtime/source-hardness hypothesis is assumed.
-/
namespace HiddenCircuits.GraphReduction
open Complexity
open Runtime.WordGraph

/-- Every graph in the previously established rational class belongs to the
natural real class, on the same labeled vertices. -/
theorem unitIntervalGraph_real {V : Type} {G : SimpleGraph V}
    (hG : UnitIntervalGraph G) : RealUnitInterval.UnitIntervalGraph G :=
  ⟨hG.some.toReal⟩

/-- The actual matrix-encoded clique-probe queries have closed real unit
interval representations, including every coincident probe copy. -/
theorem unitGraphInput_realUnit {p : ℕ} (ps : List (CutPair p))
    (S T : State (2 * p) p) (s : ℕ) :
    RealUnitInterval.UnitIntervalGraph
      (unitGraphInput (fun i => ps.get i) S T s).2.graph :=
  ⟨(unitMatrixRepresentation ps S T s).toReal⟩

/-- The existing physical graph-only oracle driver is correct for every
oracle on the full natural real unit-interval graph class. -/
theorem realUnit_wordSolverSpec (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => RealUnitInterval.UnitIntervalGraph G.2.graph) g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec
      (CliqueDriver.program .unit) g (CliqueDriver.time .unit) := by
  intro w
  apply CliqueDriver.program_executes .unit g w
  intro _ q
  exact hg (CliqueRecovery.query false w q) (unitGraphInput_realUnit _ _ _ _)

/-- Machine-grounded #P hardness for ordinary graph input under the semantic
real unit-interval promise. -/
theorem realUnit_matching_sharpPHard (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => RealUnitInterval.UnitIntervalGraph G.2.graph) g) :
    SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard (CliqueDriver.program .unit) g
    (CliqueDriver.time .unit) (realUnit_wordSolverSpec g hg)

/-- Natural real unit-interval perfect-matching counting is #P-complete in the
explicit class/promise sense: a total #P extension exists and every oracle
agreeing on promised ordinary graph encodings is #P-hard. -/
theorem realUnit_matching_sharpPComplete :
    ClassMatchingSharpPComplete (fun G => RealUnitInterval.UnitIntervalGraph G.2.graph) :=
  ⟨⟨GraphInput.perfectMatchingProblem,
      GraphVerifier.MatchingRuntime.perfectMatching_sharpP, classMatchingOracle_full _⟩,
    realUnit_matching_sharpPHard⟩

end HiddenCircuits.GraphReduction
