import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointBounds
import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointSemantics

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock
lemma program_polynomial (g : BitString→ℕ) (R : List VertexRecord) :
    ∃c,program.Executes g (initial R) (clean R (bits R)) c ∧
      c≤timePolynomial.eval (R.length+(encodeBitList (R.map encodeVertex)).length) := by
  simpa only [computedBits_eq_bits] using program_computed_polynomial g R
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
