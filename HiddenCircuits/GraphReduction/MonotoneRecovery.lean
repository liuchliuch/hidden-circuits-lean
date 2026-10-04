import HiddenCircuits.GraphReduction.MonotoneSize

/-! The finite shared-parameter oracle recovery on the actual Section 9 query graphs. -/
namespace HiddenCircuits.GraphReduction

/-- Exactly 2ph+1 oracle values, normalized by (s!)^h, then evaluated at -1. -/
noncomputable def recoverMonotoneTarget {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) : ℚ :=
  (-1 : ℚ)^(p*h) *
    (Complexity.interpolateValues (2*p*h)
      (fun s => (perfectMatchingCount (monotoneQueryGraph pairs S T s.val) : ℚ) /
        (s.val.factorial : ℚ)^h)).eval (-1)

/-- Every sample in the recovery expression is an actual unweighted graph count. -/
theorem monotoneProbe_sample {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    (probePolynomial (retainedQueryRelation pairs S T) (retainedEvenAttachment S T) oddAttachment).eval
        (s : ℚ) = (perfectMatchingCount (monotoneQueryGraph pairs S T s) : ℚ) /
      (s.factorial : ℚ)^h := by
  simpa only [Fintype.card_fin] using probePolynomial_count (retainedQueryRelation pairs S T)
    (retainedEvenAttachment S T) oddAttachment s

/-- The query counts recover the target retained-layer matching count exactly. -/
theorem recoverMonotoneTarget_correct {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) :
    recoverMonotoneTarget pairs S T =
      (perfectMatchingCount (cutGraph (retainedTargetRelation pairs S T)) : ℚ) := by
  unfold recoverMonotoneTarget
  have hn : (fun s : Fin (2*p*h+1) =>
      (perfectMatchingCount (monotoneQueryGraph pairs S T s.val) : ℚ) / (s.val.factorial : ℚ)^h) =
      (fun s => (probePolynomial (retainedQueryRelation pairs S T)
        (retainedEvenAttachment S T) oddAttachment).eval (Complexity.interpolationNode s)) := by
    funext s
    exact (monotoneProbe_sample pairs S T s.val).symm
  rw [hn,Complexity.interpolateValues_correct _ _ (monotoneProbe_degree hh pairs S T),
    monotone_probe_cancellation hh,← mul_assoc,pairedLayer_first_sign,one_mul]

end HiddenCircuits.GraphReduction
