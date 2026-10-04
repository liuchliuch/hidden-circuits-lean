import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphProgram
import HiddenCircuits.Complexity.GraphVerifier.MatchingPullback

/-! Represented-input #P membership, using only the coordinate bytes. -/
namespace HiddenCircuits.GraphReduction
open Complexity

/-- A total #P extension of the coordinate-input promise. Malformed strings are
interpreted permissively by the bounded parser; canonical representations retain
exactly their labelled graph and its perfect matchings. -/
noncomputable def unitCoordinateProblem : BitString → ℕ :=
  GraphInput.perfectMatchingProblem ∘ Runtime.CoordinateGraph.bits

theorem unitCoordinateProblem_sharpP : SharpP unitCoordinateProblem :=
  GraphVerifier.MatchingPullback.sharpP_of_graph_compiler Runtime.CoordinateGraph.program
    Runtime.CoordinateGraph.program_queryFree Runtime.CoordinateGraph.bits Runtime.CoordinateGraph.time Runtime.CoordinateGraph.size
    (Runtime.CoordinateGraph.program_executes (fun _=>0)) Runtime.CoordinateGraph.size_bound

theorem unitCoordinateProblem_oracle : UnitCoordinateOracle unitCoordinateProblem := by
  intro G R
  simp only [unitCoordinateProblem,Function.comp_apply,Runtime.CoordinateGraph.bits_representation,
    GraphInput.perfectMatchingProblem,GraphInput.decode_encode]

theorem unitCoordinateProblem_sharpPHard : SharpPHard unitCoordinateProblem :=
  unitCoordinate_counting_sharpPHard unitCoordinateProblem unitCoordinateProblem_oracle

theorem unitCoordinate_has_sharpP_complete_extension :
    ∃f : BitString → ℕ,SharpP f ∧SharpPHard f ∧UnitCoordinateOracle f :=
  ⟨unitCoordinateProblem,unitCoordinateProblem_sharpP,unitCoordinateProblem_sharpPHard,unitCoordinateProblem_oracle⟩
end HiddenCircuits.GraphReduction
