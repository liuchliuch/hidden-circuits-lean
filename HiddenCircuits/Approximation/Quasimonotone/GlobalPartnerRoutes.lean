import HiddenCircuits.Approximation.Quasimonotone.PhaseRegions
import HiddenCircuits.Approximation.Quasimonotone.PartnerRoutes
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open CanonicalPaths FiniteChains.MonotoneSwitch
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {G : SimpleGraph (Fin n)} (P Q : PerfectPartner G)
def PartnerTrafficGood (Z : PerfectPartner G) : Prop :=
  ∃ active : Fin n,PartnerInterrupted P Q Z active ∧ HasPartnerCompanion P Q Z 30
theorem partner_phase_good (active : Fin n) : PartnerTrafficGood P Q (partnerPhase P Q active.val) := by
  refine ⟨active,fun _ _ => rfl,partnerPhase Q P active.val,∅,by simp,?_⟩
  intro x _
  simpa only [Finset.ext_iff,Finset.mem_insert,Finset.mem_singleton]
    using partnerPhase_complement P Q active.val x
theorem leftSide_card_pos (active : Fin n) : 0<Fintype.card (LeftSide P Q active) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨active,Equiv.Perm.SameCycle.refl _ _⟩⟩
theorem leftSide_card_le (active : Fin n) : Fintype.card (LeftSide P Q active) ≤ n := by
  simpa using Fintype.card_le_of_injective (fun x : LeftSide P Q active => x.val) Subtype.val_injective
variable (hG : Quasimonotone G)
include hG
theorem partner_stage_route (active : Fin n) :
    ∃ l ≤ routeLength n,MarkedPartnerRoute (PartnerTrafficGood P Q)
      (partnerPhase P Q active.val) (partnerPhase P Q (active.val+1)) l := by
  by_cases hrep : partnerComponentMin P Q active=active
  · obtain ⟨l,hl,hr⟩ := all_pairs_marked_route (cutEndpoints P Q active hG)
      (sourceState P Q active hG) (targetState P Q active hG) (leftSide_card_pos P Q active)
    have hbound : l ≤ routeLength n := by
      apply hl.trans
      unfold routeLength
      have hc := leftSide_card_le P Q active
      gcongr
    refine ⟨l,hbound,?_⟩
    have hm : MarkedPartnerRoute (PartnerTrafficGood P Q)
        (stageMatching P Q hG active (sourceState P Q active hG))
        (stageMatching P Q hG active (targetState P Q active hG)) l := by
      apply MarkedPartnerRoute.ofLocalRoute (stageMatching P Q hG active) ?_ ?_ hr
      · intro s hs
        obtain ⟨_,_,hc⟩ := hs
        exact ⟨active,stageMatching_interrupted P Q hG active s,stageMatching_companion P Q hG active hc⟩
      · intro s t hst
        exact componentMatching_move P Q active hG _ _ hst
    simpa only [stageMatching_source P Q hG active hrep,stageMatching_target P Q hG active hrep] using hm
  · rw [phase_unchanged_nonrepresentative P Q active hrep]
    exact ⟨0,Nat.zero_le _,MarkedPartnerRoute.nil _ (partner_phase_good P Q active)⟩
theorem partner_prefix_route (hn : 0<n) (k : ℕ) (hk : k ≤ n) :
    ∃ l ≤ k*routeLength n,MarkedPartnerRoute (PartnerTrafficGood P Q)
      (partnerPhase P Q 0) (partnerPhase P Q k) l := by
  induction k with
  | zero => exact ⟨0,by simp,MarkedPartnerRoute.nil _ (partner_phase_good P Q ⟨0,hn⟩)⟩
  | succ k ih =>
    obtain ⟨a,ha,hra⟩ := ih (by omega)
    obtain ⟨b,hb,hrb⟩ := partner_stage_route P Q hG ⟨k,by omega⟩
    exact ⟨a+b,by nlinarith,hra.append hrb⟩
theorem all_pairs_partner_route (hn : 0<n) :
    ∃ l ≤ n*routeLength n,MarkedPartnerRoute (PartnerTrafficGood P Q) P Q l := by
  obtain ⟨l,hl,hr⟩ := partner_prefix_route P Q hG hn n le_rfl
  exact ⟨l,hl,by simpa only [partnerPhase_zero,partnerPhase_full] using hr⟩
end HiddenCircuits.Approximation.QuasimonotoneProof
