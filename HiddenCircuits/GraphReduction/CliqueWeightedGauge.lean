import HiddenCircuits.GraphReduction.PartnerGauge
import HiddenCircuits.GraphReduction.CliqueWeightedIndicator

/-! Undirected endpoint gauges and zero-one graph matching semantics. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
variable {V : Type*} [Fintype V]

 theorem partnerWeight_gauge {G : SimpleGraph V} (p : PerfectPartner G) (w : V → V → ℚ) (a : V → ℚ) :
    partnerWeight (fun u v => a u*w u v*a v) p = (∏ v, a v) * partnerWeight w p := by
  classical
  unfold partnerWeight
  calc
    (∏ e : PartnerEdge p, a e.val*w e.val (p.val e.val)*a (p.val e.val)) =
        ∏ e : PartnerEdge p, (a e.val*a (p.val e.val))*w e.val (p.val e.val) := by
      apply Finset.prod_congr rfl
      intro e _
      ring
    _ = _ := by rw [Finset.prod_mul_distrib,partnerEndpoint_product]

 theorem weightedPerfectMatchingCount_gauge (w : V → V → ℚ) (a : V → ℚ) :
    weightedPerfectMatchingCount (fun u v => a u*w u v*a v) =
      (∏ v, a v)*weightedPerfectMatchingCount w := by
  unfold weightedPerfectMatchingCount
  simp_rw [partnerWeight_gauge]
  exact (Finset.mul_sum ..).symm

/-- The signed count of an actual graph is a fixed endpoint factor times its true PM count. -/
theorem weightedPerfectMatchingCount_signed_graph (G : SimpleGraph V) (a : V → ℚ) :
    weightedPerfectMatchingCount (fun u v => a u*undirectedIndicator G u v*a v) =
      (∏ v, a v)*(perfectMatchingCount G : ℚ) := by
  rw [weightedPerfectMatchingCount_gauge,weightedPerfectMatchingCount_indicator]

/-- Diagonal entries are never used: each factor is an actual loopless matching edge. -/
theorem weightedPerfectMatchingCount_congr_on_ne (w z : V → V → ℚ)
    (h : ∀ u v, u≠v → w u v=z u v) :
    weightedPerfectMatchingCount w=weightedPerfectMatchingCount z := by
  classical
  unfold weightedPerfectMatchingCount
  apply Finset.sum_congr rfl
  intro p _
  unfold partnerWeight
  apply Finset.prod_congr rfl
  intro e _
  exact h e.val (p.val e.val) (partner_ne p e.val).symm

end HiddenCircuits.GraphReduction
