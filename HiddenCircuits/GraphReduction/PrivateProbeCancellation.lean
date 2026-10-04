import HiddenCircuits.GraphReduction.PrivateProbeVertices
import HiddenCircuits.GraphReduction.CliqueProbeIdentity
import HiddenCircuits.GraphReduction.CliqueWeightedGauge

/-! Exact private-layer clique cancellation of Section11. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

 theorem private_attachment_sum {V I : Type*} [Fintype I] (tag : V → I) (u v : V) :
    (∑ i, if tag u=i ∧ tag v=i then (1 : ℚ) else 0) = if tag u=tag v then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single (tag u)]
  · simp [eq_comm]
  · intro i _ hi; simp [Ne.symm hi]
  · simp

namespace PrivateProbe

/-- The private probes cancel every intralayer edge and leave all original cut edges unchanged. -/
theorem probeWeight_target {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (u v : RetainedOriginal p h S T) (hne : u≠v) :
    cliqueProbeWeight (retainedCliqueGraph pairs S T) (fun i v => retainedLayer S T v=i) u v =
      undirectedIndicator (cutGraph (retainedTargetRelation pairs S T)) u v := by
  rw [cliqueProbeWeight,private_attachment_sum]
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      have ht : x.val.1=y.val.1 → x.val.2≠y.val.2 := by
        intro h1 h2
        exact hne (congrArg Sum.inl (Subtype.ext (Prod.ext h1 h2)))
      by_cases hl : x.val.1=y.val.1
      · simp [retainedCliqueGraph,cliqueGraph,originalEmbedding,retainedLayer,layerTag,
          undirectedIndicator,cutGraph,hl,ht hl]
      · simp [retainedCliqueGraph,cliqueGraph,originalEmbedding,retainedLayer,layerTag,
          undirectedIndicator,cutGraph,hl]
    | inr y =>
      simp [retainedCliqueGraph,cliqueGraph,originalEmbedding,retainedLayer,layerTag,
        undirectedIndicator,cutGraph,retainedTargetRelation]
  | inr x =>
    cases v with
    | inl y =>
      simp [retainedCliqueGraph,cliqueGraph,originalEmbedding,retainedLayer,layerTag,
        undirectedIndicator,cutGraph,retainedTargetRelation]
    | inr y =>
      have ht : x.1=y.1 → x.2≠y.2 := by
        intro h1 h2
        exact hne (congrArg Sum.inr (Prod.ext h1 h2))
      by_cases hl : x.1=y.1
      · simp [retainedCliqueGraph,cliqueGraph,originalEmbedding,retainedLayer,layerTag,
          undirectedIndicator,cutGraph,hl,ht hl]
      · simp [retainedCliqueGraph,cliqueGraph,originalEmbedding,retainedLayer,layerTag,
          undirectedIndicator,cutGraph,hl]

/-- Exact cancellation to the actual target graph count, with no additional sign. -/
theorem probe_cancellation {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    (cliqueProbePolynomial (retainedCliqueGraph pairs S T) (fun i v => retainedLayer S T v=i)).eval (-1) =
      (perfectMatchingCount (cutGraph (retainedTargetRelation pairs S T)) : ℚ) := by
  rw [cliqueProbe_cancellation]
  rw [weightedPerfectMatchingCount_congr_on_ne _ _ (probeWeight_target pairs S T),
    weightedPerfectMatchingCount_indicator]

end PrivateProbe
end HiddenCircuits.GraphReduction
