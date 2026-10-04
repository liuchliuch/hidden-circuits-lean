import HiddenCircuits.Approximation.Quasimonotone.GlobalPartnerRoutes
import HiddenCircuits.Approximation.Quasimonotone.PartnerTraffic
import HiddenCircuits.Approximation.FiniteChains.Sampling
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open CanonicalPaths FiniteChains
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {n : ℕ} (G : SimpleGraph (Fin n)) (hG : Quasimonotone G)
abbrev PartnerState := PerfectPartner G
def partnerRouteLength (n : ℕ) : ℕ := n*(n*(8*n*n+4))
def partnerTrafficFactor (n : ℕ) : ℕ := partnerRouteLength n*((n+1)^30*n^30*n^30*n*n)
include hG in
/-- Every recorded edge comes from a genuine admissible switch. -/
theorem constructed_partner_path (P Q : PartnerState G) :
    ∃ path : FiniteChains.Path P Q, path.length ≤ partnerRouteLength n ∧
      (∀ i : Fin path.length, PartnerMove (path.vertex i.castSucc) (path.vertex i.succ)) ∧
      ∀ i : Fin path.length, PartnerTrafficGood P Q (path.vertex i.castSucc) := by
  by_cases hn : 0<n
  · obtain ⟨l,hl,hr⟩ := all_pairs_partner_route P Q hG hn
    obtain ⟨v,hv₀,hvlast,hvmove,hvGood⟩ := hr.vertices
    exact ⟨⟨l,v,hv₀,hvlast⟩,hl,hvmove,fun i => hvGood i.castSucc⟩
  · have hz : n=0 := by omega
    have he : P=Q := by
      apply Subtype.ext
      funext i
      have hi := i.isLt
      omega
    refine ⟨⟨0,fun _ => P,rfl,he⟩,by simp [partnerRouteLength],?_,?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
noncomputable def partnerFlowPath (P Q : PartnerState G) : FiniteChains.Path P Q :=
  (constructed_partner_path G hG P Q).choose
theorem partnerFlowPath_length (P Q : PartnerState G) : (partnerFlowPath G hG P Q).length ≤ partnerRouteLength n :=
  (constructed_partner_path G hG P Q).choose_spec.1
theorem partnerFlowPath_move (P Q : PartnerState G) (i : Fin (partnerFlowPath G hG P Q).length) :
    PartnerMove ((partnerFlowPath G hG P Q).vertex i.castSucc) ((partnerFlowPath G hG P Q).vertex i.succ) :=
  (constructed_partner_path G hG P Q).choose_spec.2.1 i
theorem partnerFlowPath_good (P Q : PartnerState G) (i : Fin (partnerFlowPath G hG P Q).length) :
    PartnerTrafficGood P Q ((partnerFlowPath G hG P Q).vertex i.castSucc) :=
  (constructed_partner_path G hG P Q).choose_spec.2.2 i
theorem partnerFlowPath_edgeCount_le (P Q a b : PartnerState G) :
    (partnerFlowPath G hG P Q).edgeCount a b ≤ partnerRouteLength n := by
  classical
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin (partnerFlowPath G hG P Q).length))
    (fun i => (partnerFlowPath G hG P Q).vertex i.castSucc=a ∧ (partnerFlowPath G hG P Q).vertex i.succ=b)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  unfold FiniteChains.Path.edgeCount
  convert h.trans (partnerFlowPath_length G hG P Q) using 1
theorem partnerFlowPath_edgeCount_zero (P Q a b : PartnerState G) (hgood : ¬PartnerTrafficGood P Q a) :
    (partnerFlowPath G hG P Q).edgeCount a b=0 := by
  classical
  unfold FiniteChains.Path.edgeCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hp : (partnerFlowPath G hG P Q).vertex i.castSucc=a ∧ (partnerFlowPath G hG P Q).vertex i.succ=b := by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hg := partnerFlowPath_good G hG P Q i
  rw [hp.1] at hg
  exact hgood hg
theorem traffic_pairs_card (a : PartnerState G) :
    Fintype.card (PartnerTraffic.Pairs a 30)=
      ∑ P : PartnerState G, ∑ Q : PartnerState G, if PartnerTrafficGood P Q a then 1 else 0 := by
  classical
  rw [← Fintype.sum_prod_type (fun t : PartnerState G × PartnerState G =>
    if PartnerTrafficGood t.1 t.2 a then 1 else 0)]
  rw [Fintype.card_eq_nat_card]
  change Nat.card {t : PartnerState G × PartnerState G // PartnerTrafficGood t.1 t.2 a} = _
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype,Finset.card_filter]
theorem partnerFlowPath_traffic (a b : PartnerState G) :
    FiniteChains.traffic (partnerFlowPath G hG) a b ≤ partnerTrafficFactor n*Fintype.card (PartnerState G) := by
  have hc := PartnerTraffic.pairs_card_bound a 30
  calc
    FiniteChains.traffic (partnerFlowPath G hG) a b ≤
        ∑ P : PartnerState G, ∑ Q : PartnerState G,
          if PartnerTrafficGood P Q a then partnerRouteLength n else 0 := by
      apply Finset.sum_le_sum
      intro P _
      apply Finset.sum_le_sum
      intro Q _
      by_cases h : PartnerTrafficGood P Q a
      · simpa only [if_pos h] using partnerFlowPath_edgeCount_le G hG P Q a b
      · simp only [if_neg h,partnerFlowPath_edgeCount_zero G hG P Q a b h,le_refl]
    _ = partnerRouteLength n*Fintype.card (PartnerTraffic.Pairs a 30) := by
      rw [traffic_pairs_card]
      simp_rw [Finset.mul_sum,mul_ite,mul_one,mul_zero]
    _ ≤ partnerRouteLength n*(Fintype.card (PartnerState G)*((n+1)^30*n^30*n^30)*n*n) :=
      Nat.mul_le_mul_left _ hc
    _ = partnerTrafficFactor n*Fintype.card (PartnerState G) := by unfold partnerTrafficFactor; ring
end HiddenCircuits.Approximation.QuasimonotoneProof
