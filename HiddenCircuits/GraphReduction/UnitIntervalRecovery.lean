import HiddenCircuits.GraphReduction.UnitIntervalCancellation
import HiddenCircuits.GraphReduction.MonotoneTargetBridge

/-! Exact Section10 recovery of actual PairEval from the literal unweighted clique-probe queries. -/
namespace HiddenCircuits.GraphReduction

/-- Explicit shared even-node oracle postprocessing, with the final fixed sign. -/
noncomputable def recoverUnitIntervalTarget {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) : ℚ :=
  (-1 : ℚ)^(p*h) * (interpolateCliqueValues (2*p*h)
    (fun t => (perfectMatchingCount (unitIntervalQueryGraph pairs S T (2*t.val)) : ℚ) /
      (oddFactorial t.val : ℚ)^(h+1))).eval (-1)

 theorem unitIntervalProbe_sample {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (t : ℕ) :
    (cliqueProbePolynomial (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T)).eval (2*t : ℚ) =
      (perfectMatchingCount (unitIntervalQueryGraph pairs S T (2*t)) : ℚ) /
        (oddFactorial t : ℚ)^(h+1) := by
  simpa only [Fintype.card_fin] using cliqueProbePolynomial_count
    (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T) t

 theorem recoverUnitIntervalTarget_correct {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) : recoverUnitIntervalTarget pairs S T =
      (perfectMatchingCount (cutGraph (retainedTargetRelation pairs S T)) : ℚ) := by
  unfold recoverUnitIntervalTarget
  have hn : (fun t : Fin (2*p*h+1) =>
      (perfectMatchingCount (unitIntervalQueryGraph pairs S T (2*t.val)) : ℚ) /
        (oddFactorial t.val : ℚ)^(h+1)) =
      (fun t => (cliqueProbePolynomial (unitIntervalOriginalGraph pairs S T)
        (unitIntervalAttachment S T)).eval (cliqueInterpolationNode t)) := by
    funext t
    exact (unitIntervalProbe_sample pairs S T t.val).symm
  rw [hn,interpolateCliqueValues_correct _ _ (unitIntervalProbe_degree hh pairs S T),
    unitInterval_probe_cancellation hh,← mul_assoc,pairedLayer_first_sign,one_mul]

noncomputable def recoverPairFromUnitIntervals {p : ℕ} (w : List (CutPair p))
    (S T : State (2*p) p) : ℚ := recoverUnitIntervalTarget (fun r => w.get r) S T

/-- The graph count is connected to the actual paired permanental-compound product. -/
theorem recoverPairFromUnitIntervals_correct {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) : recoverPairFromUnitIntervals w S T=pairWordMatrix w S T := by
  unfold recoverPairFromUnitIntervals
  rw [recoverUnitIntervalTarget_correct (List.length_pos_iff.mpr hw),retainedTarget_matchingCount]

end HiddenCircuits.GraphReduction
