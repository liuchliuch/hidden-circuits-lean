import HiddenCircuits.GraphReduction.CliqueProbeInterpolation
import HiddenCircuits.GraphReduction.CliqueWeightedExpansion

/-! Full Section10 clique-probe cancellation, for actual simple unweighted graphs. -/
namespace HiddenCircuits.GraphReduction
open Polynomial
variable {V I : Type*} [Fintype V] [Fintype I]

/-- Negative evaluation equals the genuinely edge-weighted complete-graph matching sum. -/
theorem cliqueProbe_cancellation (G : SimpleGraph V) (A : I → V → Prop) :
    (cliqueProbePolynomial G A).eval (-1) =
      weightedPerfectMatchingCount (cliqueProbeWeight G A) := by
  rw [cliqueProbePolynomial_negative,weightedPerfectMatchingCount_clique_blocks]

/-- Lemma10.2, including arbitrary overlapping neighborhoods, every even sample,
the degree bound and the actual negative weighted-matching interpretation. -/
theorem cliqueProbe_identity (G : SimpleGraph V) (A : I → V → Prop) :
    ∃ Ψ : ℚ[X], Ψ.natDegree≤Fintype.card V/2 ∧
      (∀ t : ℕ, Ψ.eval (2*t : ℚ) = (perfectMatchingCount (cliqueProbeGraph G A (2*t)) : ℚ) /
        (oddFactorial t : ℚ)^Fintype.card I) ∧
      Ψ.eval (-1)=weightedPerfectMatchingCount (cliqueProbeWeight G A) :=
  ⟨cliqueProbePolynomial G A,cliqueProbePolynomial_degree G A,cliqueProbePolynomial_count G A,
    cliqueProbe_cancellation G A⟩

/-- The finite even-node Lagrange procedure recovers that count from genuine unweighted queries. -/
theorem recoverCliqueProbe_correct (G : SimpleGraph V) (A : I → V → Prop) :
    recoverCliqueProbe G A = weightedPerfectMatchingCount (cliqueProbeWeight G A) := by
  rw [recoverCliqueProbe_polynomial,cliqueProbe_cancellation]

end HiddenCircuits.GraphReduction
