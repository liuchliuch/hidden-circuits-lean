import HiddenCircuits.GraphReduction.UnitIntervalSize
import HiddenCircuits.GraphReduction.CliqueProbeIdentity
import HiddenCircuits.GraphReduction.CliqueWeightedGauge

/-! The literal Section10 probe subtraction removes intralayer edges and flips only first cuts. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Each original vertex belongs to exactly one of the h+1 probe neighborhoods. -/
def unitPairIndex {p h : ℕ} {S T : State (2*p) p} : UnitOriginalVertex p h S T → Fin (h+1)
  | .inl x => x.val.1
  | .inr y => y.1.castSucc

 theorem unit_attachment_sum {p h : ℕ} (S T : State (2*p) p)
    (u v : UnitOriginalVertex p h S T) :
    (∑ r, if unitIntervalAttachment S T r u ∧ unitIntervalAttachment S T r v then (1 : ℚ) else 0) =
      if unitPairIndex u=unitPairIndex v then 1 else 0 := by
  classical
  have hc (r : Fin (h+1)) (v : UnitOriginalVertex p h S T) :
      unitIntervalAttachment S T r v ↔ unitPairIndex v=r := by cases v <;> rfl
  simp_rw [hc]
  rw [Finset.sum_eq_single (unitPairIndex u)]
  · simp [eq_comm]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

 theorem unitFirstCut_sign (r : ℕ) : (-1 : ℚ)^r * (-1 : ℚ)^(r+1)= -1 := by
  rw [mul_comm,pairedLayer_second_sign]

 theorem unitInterval_cross_weight {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (x : RetainedEven p h S T) (y : OddVertex (2*p) h) :
    cliqueProbeWeight (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T) (.inl x) (.inr y) =
      unitEndpointSign (.inl x : UnitOriginalVertex p h S T) *
        undirectedIndicator (cutGraph (retainedTargetRelation pairs S T)) (.inl x) (.inr y) *
          unitEndpointSign (.inr y : UnitOriginalVertex p h S T) := by
  rw [cliqueProbeWeight,unit_attachment_sum]
  simp only [unitPairIndex,Fin.ext_iff,Fin.val_castSucc]
  by_cases hf : x.val.1.val=y.1.val
  · by_cases he : (pairs y.1).first x.val.2 y.2=1
    · simp [unitIntervalOriginalGraph,unitIntervalCrossRelation,undirectedIndicator,cutGraph,
        retainedTargetRelation,targetRelation,unitEndpointSign,hf,he,unitFirstCut_sign]
    · simp [unitIntervalOriginalGraph,unitIntervalCrossRelation,undirectedIndicator,cutGraph,
        retainedTargetRelation,targetRelation,unitEndpointSign,hf,he]
  · by_cases hs : x.val.1.val=y.1.val+1
    · by_cases he : (pairs y.1).second y.2 x.val.2=1
      · simp [unitIntervalOriginalGraph,unitIntervalCrossRelation,undirectedIndicator,cutGraph,
          retainedTargetRelation,targetRelation,unitEndpointSign,hs,he,pairedLayer_first_sign]
      · simp [unitIntervalOriginalGraph,unitIntervalCrossRelation,undirectedIndicator,cutGraph,
          retainedTargetRelation,targetRelation,unitEndpointSign,hs,he]
    · simp [unitIntervalOriginalGraph,unitIntervalCrossRelation,undirectedIndicator,cutGraph,
        retainedTargetRelation,targetRelation,unitEndpointSign,hf,hs]

/-- Equality on every possible undirected matching edge, including all intralayer cancellations. -/
theorem unitInterval_probeWeight {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (u v : UnitOriginalVertex p h S T) (hne : u≠v) :
    cliqueProbeWeight (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T) u v =
      unitEndpointSign u * undirectedIndicator (cutGraph (retainedTargetRelation pairs S T)) u v *
        unitEndpointSign v := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      have ht : x.val.1=y.val.1 → x.val.2≠y.val.2 := by
        intro h1 h2
        exact hne (congrArg Sum.inl (Subtype.ext (Prod.ext h1 h2)))
      rw [cliqueProbeWeight,unit_attachment_sum]
      by_cases hl : x.val.1=y.val.1
      · simp [unitIntervalOriginalGraph,unitPairIndex,undirectedIndicator,cutGraph,hl,ht hl]
      · simp [unitIntervalOriginalGraph,unitPairIndex,undirectedIndicator,cutGraph,hl]
    | inr y => exact unitInterval_cross_weight pairs S T x y
  | inr x =>
    cases v with
    | inl y =>
      rw [cliqueProbeWeight_symmetric,unitInterval_cross_weight]
      simp only [undirectedIndicator,SimpleGraph.adj_comm]
      ring
    | inr y =>
      have ht : x.1=y.1 → x.2≠y.2 := by
        intro h1 h2
        exact hne (congrArg Sum.inr (Prod.ext h1 h2))
      rw [cliqueProbeWeight,unit_attachment_sum]
      by_cases hl : x.1=y.1
      · simp [unitIntervalOriginalGraph,unitPairIndex,undirectedIndicator,cutGraph,hl,ht hl]
      · have hc : x.1.castSucc≠y.1.castSucc := fun he => hl (Fin.castSucc_injective _ he)
        simp [unitIntervalOriginalGraph,unitPairIndex,undirectedIndicator,cutGraph,hl,hc]

/-- The actual Section10 query polynomial cancels to the signed target matching count. -/
theorem unitInterval_probe_cancellation {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) :
    (cliqueProbePolynomial (unitIntervalOriginalGraph pairs S T) (unitIntervalAttachment S T)).eval (-1) =
      (-1 : ℚ)^(p*h) * (perfectMatchingCount (cutGraph (retainedTargetRelation pairs S T)) : ℚ) := by
  rw [cliqueProbe_cancellation]
  rw [weightedPerfectMatchingCount_congr_on_ne _ _ (unitInterval_probeWeight pairs S T)]
  rw [weightedPerfectMatchingCount_signed_graph,unitEndpoint_sign hh]

end HiddenCircuits.GraphReduction
