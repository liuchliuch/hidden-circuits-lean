import HiddenCircuits.GraphReduction.MonotoneGauge

/-! The constant sign statement for each actual target perfect matching. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators

/-- Every surviving matching term has the same sign, with no matching-count premise. -/
theorem monotone_matching_weight {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (e : CutBijection (retainedTargetRelation pairs S T)) :
    (∏ x, probeWeight (retainedQueryRelation pairs S T) (retainedEvenAttachment S T)
      oddAttachment x (e.val x)) = (-1 : ℚ)^(p*h) := by
  classical
  simp_rw [retained_monotone_probeWeight]
  have hi (x : RetainedEven p h S T) :
      edgeIndicator (retainedTargetRelation pairs S T) x (e.val x)=1 := by
    simp [edgeIndicator,e.property x]
  simp_rw [hi,mul_one]
  have he : (∏ x, (-1 : ℚ)^(e.val x).1.val) = ∏ y : OddVertex (2*p) h, (-1 : ℚ)^y.1.val :=
    e.val.prod_comp (fun y => (-1 : ℚ)^y.1.val)
  rw [Finset.prod_mul_distrib,he]
  exact monotone_endpoint_sign hh S T

/-- The sign statement expressed directly for mathlib's perfect matching subgraphs. -/
theorem monotone_perfectMatching_weight {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (m : PerfectMatching (cutGraph (retainedTargetRelation pairs S T))) :
    (∏ x, probeWeight (retainedQueryRelation pairs S T) (retainedEvenAttachment S T)
      oddAttachment x ((cutPerfectMatchingEquiv _ m).val x)) = (-1 : ℚ)^(p*h) :=
  monotone_matching_weight hh pairs S T (cutPerfectMatchingEquiv _ m)

end HiddenCircuits.GraphReduction
