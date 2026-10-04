import HiddenCircuits.GraphReduction.PrivateProbeCancellation
import HiddenCircuits.GraphReduction.UnitIntervalSize
import HiddenCircuits.GraphReduction.MonotoneTargetBridge

/-! Shared even-node recovery of actual paired transfers from the Section11 private-probe graphs. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe

 theorem probe_layer_card (h : ℕ) : Fintype.card (Layer h)=2*h+1 := by
  simp only [Layer,Fintype.card_sum,Fintype.card_fin]
  omega

 theorem probe_degree {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    (cliqueProbePolynomial (retainedCliqueGraph pairs S T) (fun i v => retainedLayer S T v=i)).natDegree≤2*p*h := by
  simpa only [unitOriginal_half_card hh] using cliqueProbePolynomial_degree
    (retainedCliqueGraph pairs S T) (fun i v => retainedLayer S T v=i)

 theorem probe_sample {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (t : ℕ) :
    (cliqueProbePolynomial (retainedCliqueGraph pairs S T) (fun i v => retainedLayer S T v=i)).eval (2*t : ℚ) =
      (perfectMatchingCount (retainedQueryGraph pairs S T (2*t)) : ℚ) /
        (oddFactorial t : ℚ)^(2*h+1) := by
  simpa only [probe_layer_card] using cliqueProbePolynomial_count
    (retainedCliqueGraph pairs S T) (fun i v => retainedLayer S T v=i) t

/-- Exactly2ph+1 actual simple-unweighted query counts, all at nonnegative even sizes. -/
noncomputable def recoverTarget {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) : ℚ :=
  (interpolateCliqueValues (2*p*h)
    (fun t => (perfectMatchingCount (retainedQueryGraph pairs S T (2*t.val)) : ℚ) /
      (oddFactorial t.val : ℚ)^(2*h+1))).eval (-1)

 theorem recoverTarget_correct {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) : recoverTarget pairs S T =
      (perfectMatchingCount (cutGraph (retainedTargetRelation pairs S T)) : ℚ) := by
  unfold recoverTarget
  have hn : (fun t : Fin (2*p*h+1) =>
      (perfectMatchingCount (retainedQueryGraph pairs S T (2*t.val)) : ℚ) /
        (oddFactorial t.val : ℚ)^(2*h+1)) =
      (fun t => (cliqueProbePolynomial (retainedCliqueGraph pairs S T)
        (fun i v => retainedLayer S T v=i)).eval (cliqueInterpolationNode t)) := by
    funext t
    exact (probe_sample pairs S T t.val).symm
  rw [hn,interpolateCliqueValues_correct _ _ (probe_degree hh pairs S T),probe_cancellation]

noncomputable def recoverPair {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p) : ℚ :=
  recoverTarget (fun r => w.get r) S T

/-- Exact Section11 numerical recovery of the actual permanental-compound paired product. -/
theorem recoverPair_correct {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) : recoverPair w S T=pairWordMatrix w S T := by
  unfold recoverPair
  rw [recoverTarget_correct (List.length_pos_iff.mpr hw),retainedTarget_matchingCount]

end HiddenCircuits.GraphReduction.PrivateProbe
