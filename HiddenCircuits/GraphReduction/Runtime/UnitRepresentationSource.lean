import HiddenCircuits.GraphReduction.Runtime.UnitRepresentationPolynomial
import HiddenCircuits.GraphReduction.Runtime.UnitRepresentationCorrect

/-! The concrete coordinate encoder produces precisely the
coordinate-only bytes of the paper's source query, with no representation input. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
open Complexity Complexity.OracleBlock

theorem query_executes {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ)
    (g : BitString → ℕ) :
    ∃t,program.Executes g (initial (2*p) ps.length (unitRecords (fun r=>ps.get r) S T s))
      (Function.update (initial (2*p) ps.length (unitRecords (fun r=>ps.get r) S T s))
        7 (unitRepresentationBits ps S T s)) t ∧
      t≤timePolynomial.eval ((unitGraphInput (fun r=>ps.get r) S T s).1+
        (unitDescriptor (fun r=>ps.get r) S T s).length+2*p+ps.length) := by
  simpa only [finalState,unitRepresentationBits_eq,unitRecords_length,unitDescriptor] using
    program_polynomial (2*p) ps.length (unitRecords (fun r=>ps.get r) S T s) g
end HiddenCircuits.GraphReduction.Runtime.UnitRepresentation
