import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionProgram
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoundsCorrect
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionGateMembership

/-! Unconditional machine-grounded recognition and #P membership for the
literal ordinary-input unit-interval restricted matching count. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionProgram
open Complexity DH.Runtime.PairCheck

/-- Every raw byte string is handled: malformed input is rejected, and a valid
ordinary graph is accepted exactly when it has a real unit-interval model. -/
theorem accepts_iff (raw : BitString) : accepts raw=true ↔
    ∃G : GraphInput, GraphInput.decode raw=some G ∧ RealUnitInterval.UnitIntervalGraph G.2.graph := by
  cases hd : GraphInput.decode raw with
  | none => simp [accepts,hd]
  | some G => simp [accepts,hd,UnitRecognitionRounds.accepts_ofGraph_iff]

theorem accepts_malformed (raw : BitString) (h : GraphInput.decode raw=none) : accepts raw=false := by
  simp [accepts,h]

theorem accepts_encode (G : GraphInput) :
    accepts G.encode=true ↔ RealUnitInterval.UnitIntervalGraph G.2.graph := by
  simp [accepts,UnitRecognitionRounds.accepts_ofGraph_iff]

/-- The physical implementation computes the same total Boolean function as
the independent semantic recognizer, including malformed inputs. -/
theorem accepts_eq_semantic (raw : BitString) : accepts raw=UnitRecognitionGate.acceptsUnitGraph raw := by
  cases hd : GraphInput.decode raw with
  | none => simp [accepts,UnitRecognitionGate.acceptsUnitGraph,hd]
  | some G =>
    simp only [accepts,UnitRecognitionGate.acceptsUnitGraph,hd]
    apply Bool.eq_iff_iff.mpr
    exact (UnitRecognitionRounds.accepts_ofGraph_iff G.2).trans
      (UnitIntervalRecognition.recognize_iff G.2.graph).symm

/-- Actual mathlib finite binary-stack polynomial time, on original graph
bytes rather than a supplied ordering, interval representation, or clock. -/
theorem polynomial_recognition : PolyTime (fun raw=>Computability.encodeBool (accepts raw)) :=
  Complexity.OracleBlock.polyTime_of_block program program_queryFree time (program_executes (fun _=>0))

theorem semantic_polyVerifier : PolyVerifier UnitRecognitionGate.acceptsUnitGraph := by
  have h : accepts=UnitRecognitionGate.acceptsUnitGraph := funext accepts_eq_semantic
  rw [←h]
  exact polyVerifier

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionProgram

namespace HiddenCircuits.GraphReduction.UnitIntervalRecognition
open Complexity

/-- Literal zero on malformed input and on every valid graph outside the real
unit-interval class. The #P verifier uses a real graph-preserve-or-fixed-odd
compiler, not an assumed polynomial-time recognition predicate. -/
theorem restrictedProblem_sharpP : SharpP restrictedProblem := by
  apply Runtime.UnitRecognitionGate.restrictedProblem_sharpP_of_recognizer
    Runtime.UnitRecognitionProgram.program Runtime.UnitRecognitionProgram.program_queryFree
    Runtime.UnitRecognitionProgram.accepts Runtime.UnitRecognitionProgram.time
    (Runtime.UnitRecognitionProgram.program_executes (fun _=>0))
  intro xs G hd
  simpa only [Runtime.UnitRecognitionGate.acceptsUnitGraph,hd] using
    Runtime.UnitRecognitionProgram.accepts_eq_semantic xs

/-- Unconditional #P completeness of this specified ordinary-input total
counting function, combining actual membership and graph-only hardness. -/
theorem restrictedProblem_sharpP_complete : SharpP restrictedProblem ∧ SharpPHard restrictedProblem :=
  ⟨restrictedProblem_sharpP,restrictedProblem_sharpPHard⟩

end HiddenCircuits.GraphReduction.UnitIntervalRecognition
