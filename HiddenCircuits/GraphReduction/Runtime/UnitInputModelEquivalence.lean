import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateExtractionRawProgram
import HiddenCircuits.GraphReduction.Runtime.CoordinateGraphProgram

/-! Polynomial equivalence of ordinary labeled unit-interval graphs and native
common-denominator interval coordinates. Both directions are actual finite
binary-stack machines. The forward machine rejects malformed/nonclass graphs;
the reverse machine has the documented permissive total extension. Assertions
about representations are on their honest valid-input domains, not an assertion
that composing a count oracle through the rejection word preserves zero. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitInputModelEquivalence
open Complexity Complexity.OracleBlock UnitCoordinateExtractionResult

/-- The reverse conversion physically parses and compares signed binary data. -/
theorem coordinate_to_graph_polyTime : PolyTime CoordinateGraph.bits :=
  polyTime_of_block CoordinateGraph.program CoordinateGraph.program_queryFree
    CoordinateGraph.time (CoordinateGraph.program_executes (fun _=>0))

/-- The forward direction obtains its own recognition result, order and coordinates. -/
theorem graph_to_coordinate_polyTime : PolyTime result :=
  UnitCoordinateExtractionRaw.polynomial_graph_to_coordinates

/-- A raw accepted graph is converted to a valid native representation of the
same original vertex labels, with no representation supplied to the machine. -/
theorem recovers_representation (raw : BitString) (G : GraphInput)
    (hd : GraphInput.decode raw=some G)
    (hu : RealUnitInterval.UnitIntervalGraph G.2.graph) :
    ∃R : UnitIntegerRepresentation G, result raw=unitCoordinateBits G R := by
  exact ⟨UnitIntervalGraphInput.asIntegerInput G (representation G hu),
    (accepted hd hu).trans (bytes_representation G hu)⟩

/-- Both actual polynomial conversions and their exact valid-input roundtrips. -/
theorem polynomial_input_model_equivalence :
    PolyTime result ∧ PolyTime CoordinateGraph.bits ∧
    (∀raw G, GraphInput.decode raw=some G →
      RealUnitInterval.UnitIntervalGraph G.2.graph →
      ∃R : UnitIntegerRepresentation G, result raw=unitCoordinateBits G R) ∧
    (∀G (R : UnitIntegerRepresentation G), CoordinateGraph.bits (unitCoordinateBits G R)=G.encode) :=
  ⟨graph_to_coordinate_polyTime,coordinate_to_graph_polyTime,recovers_representation,
    CoordinateGraph.bits_representation⟩

/-- The rejection sentinel is never confused with an accepted empty graph. -/
theorem rejected_iff (raw : BitString) : result raw=[] ↔
    ¬∃G : GraphInput,GraphInput.decode raw=some G ∧ RealUnitInterval.UnitIntervalGraph G.2.graph := by
  simpa using not_congr (UnitCoordinateExtractionRaw.succeeds_iff raw)

end HiddenCircuits.GraphReduction.Runtime.UnitInputModelEquivalence
