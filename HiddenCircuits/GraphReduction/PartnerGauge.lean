import HiddenCircuits.GraphReduction.PartnerEdges

/-! Each actual matching uses each endpoint exactly once. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Multiplying the two endpoint factors over genuine undirected matching edges
is exactly the product over all vertices. -/
theorem partnerEndpoint_product (p : PerfectPartner G) (a : V → ℚ) :
    (∏ e : PartnerEdge p, a e.val * a (p.val e.val)) = ∏ v, a v := by
  classical
  calc
    (∏ e : PartnerEdge p, a e.val * a (p.val e.val)) =
        ∏ e : PartnerEdge p, ∏ b : Bool, a ((partnerVertexEquiv p).symm (e,b)) := by
      apply Finset.prod_congr rfl
      intro e _
      simp [partnerVertexEquiv,mul_comm]
    _ = ∏ e : PartnerEdge p × Bool, a ((partnerVertexEquiv p).symm e) :=
      (Fintype.prod_prod_type (fun e : PartnerEdge p × Bool => a ((partnerVertexEquiv p).symm e))).symm
    _ = _ := (partnerVertexEquiv p).symm.prod_comp a

end HiddenCircuits.GraphReduction
