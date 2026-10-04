import HiddenCircuits.Approximation.Quasimonotone.PartnerPhases
import HiddenCircuits.Approximation.Quasimonotone.CutProfiles
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open CanonicalPaths FiniteChains.MonotoneSwitch
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {G : SimpleGraph (Fin n)} (P Q : PerfectPartner G)
theorem partnerComponentMin_comm (x : Fin n) : partnerComponentMin P Q x=partnerComponentMin Q P x := by
  have hs : partnerComponentVertices P Q x=partnerComponentVertices Q P x := by
    unfold partnerComponentVertices
    rw [matchingUnion_comm]
  unfold partnerComponentMin
  simp only [hs]
theorem partnerPhase_complement (cut : ℕ) (x : Fin n) :
    ({(partnerPhase P Q cut).val x,(partnerPhase Q P cut).val x} : Finset (Fin n))={P.val x,Q.val x} := by
  change ({partnerPhaseValue P Q cut x,partnerPhaseValue Q P cut x} : Finset (Fin n))=_
  unfold partnerPhaseValue
  rw [← partnerComponentMin_comm P Q x]
  split_ifs <;> simp [Finset.pair_comm]
theorem partnerPhase_preserves_region (base : Fin n) (cut : ℕ) :
    Preserves (componentRegion P Q base) (partnerPhase P Q cut) := by
  intro x
  change x∈componentRegion P Q base ↔ partnerPhaseValue P Q cut x∈componentRegion P Q base
  unfold partnerPhaseValue
  split_ifs
  · exact target_preserves_region P Q base x
  · exact source_preserves_region P Q base x
theorem complementPhase_preserves_region (base : Fin n) (cut : ℕ) :
    Preserves (componentRegion P Q base) (partnerPhase Q P cut) := by
  intro x
  change x∈componentRegion P Q base ↔ partnerPhaseValue Q P cut x∈componentRegion P Q base
  unfold partnerPhaseValue
  split_ifs
  · exact source_preserves_region P Q base x
  · exact target_preserves_region P Q base x
theorem partnerComponentMin_idem (x : Fin n) :
    partnerComponentMin P Q (partnerComponentMin P Q x)=partnerComponentMin P Q x :=
  partnerComponentMin_eq_of_reachable (partnerComponentMin_reachable P Q x)
theorem partnerComponentMin_eq_iff (active x : Fin n)
    (hrep : partnerComponentMin P Q active=active) :
    partnerComponentMin P Q x=active ↔ (matchingUnion P Q).Reachable active x := by
  constructor
  · intro h
    simpa only [h] using partnerComponentMin_reachable P Q x
  · intro h
    exact (partnerComponentMin_eq_of_reachable h).symm.trans hrep
theorem phase_before_inside (active : Fin n) (hrep : partnerComponentMin P Q active=active)
    {x : Fin n} (hx : x∈componentRegion P Q active) :
    (partnerPhase P Q active.val).val x=P.val x := by
  have hm := (partnerComponentMin_eq_iff P Q active x hrep).mpr ((mem_componentRegion P Q active x).mp hx)
  simp [partnerPhase,partnerPhaseValue,hm]
theorem phase_after_inside (active : Fin n) (hrep : partnerComponentMin P Q active=active)
    {x : Fin n} (hx : x∈componentRegion P Q active) :
    (partnerPhase P Q (active.val+1)).val x=Q.val x := by
  have hm := (partnerComponentMin_eq_iff P Q active x hrep).mpr ((mem_componentRegion P Q active x).mp hx)
  simp [partnerPhase,partnerPhaseValue,hm]
theorem phase_unchanged_outside (active : Fin n)
    {x : Fin n} (hx : x∉componentRegion P Q active) :
    (partnerPhase P Q (active.val+1)).val x=(partnerPhase P Q active.val).val x := by
  have hm : partnerComponentMin P Q x≠active := by
    intro h
    apply hx
    apply (mem_componentRegion P Q active x).mpr
    simpa only [h] using partnerComponentMin_reachable P Q x
  have hv : (partnerComponentMin P Q x).val≠active.val := fun h => hm (Fin.ext h)
  have hi : (partnerComponentMin P Q x).val < active.val+1 ↔ (partnerComponentMin P Q x).val < active.val := by omega
  simp only [partnerPhase,partnerPhaseValue,hi]
theorem phase_unchanged_nonrepresentative (active : Fin n) (hrep : partnerComponentMin P Q active≠active) :
    partnerPhase P Q (active.val+1)=partnerPhase P Q active.val := by
  apply Subtype.ext
  funext x
  have hm : partnerComponentMin P Q x≠active := by
    intro h
    have hh := partnerComponentMin_idem P Q x
    rw [h] at hh
    exact hrep hh
  have hv : (partnerComponentMin P Q x).val≠active.val := fun h => hm (Fin.ext h)
  have hi : (partnerComponentMin P Q x).val < active.val+1 ↔ (partnerComponentMin P Q x).val < active.val := by omega
  simp only [partnerPhase,partnerPhaseValue,hi]
variable (hG : Quasimonotone G) (active : Fin n)
noncomputable def stageMatching (s : ColumnState (cutEndpoints P Q active hG)) : PerfectPartner G :=
  componentMatching P Q active hG (partnerPhase P Q active.val)
    (partnerPhase_preserves_region P Q active active.val) s
theorem stageMatching_interrupted (s : ColumnState (cutEndpoints P Q active hG)) :
    PartnerInterrupted P Q (stageMatching P Q hG active s) active := by
  intro x hx
  exact componentMatching_outside P Q active hG _ _ s (fun h => hx ((mem_componentRegion P Q active x).mp h))
theorem stageMatching_source (hrep : partnerComponentMin P Q active=active) :
    stageMatching P Q hG active (sourceState P Q active hG)=partnerPhase P Q active.val := by
  unfold stageMatching componentMatching
  apply splice_eq_of_agree_inside _ _ _ (extendCut_preserves_region P Q active _)
    (partnerPhase_preserves_region P Q active active.val)
  intro x hx
  change (cutMatching P Q active hG (sourceState P Q active hG)).val x=_
  rw [cutMatching_source,phase_before_inside P Q active hrep hx]
theorem stageMatching_target (hrep : partnerComponentMin P Q active=active) :
    stageMatching P Q hG active (targetState P Q active hG)=partnerPhase P Q (active.val+1) := by
  apply Subtype.ext
  funext x
  by_cases hx : x∈componentRegion P Q active
  · change (componentMatching P Q active hG _ _ _).val x=_
    rw [componentMatching_inside P Q active hG _ _ _ hx,cutMatching_target,
      extendCut_target_inside P Q active hx,phase_after_inside P Q active hrep hx]
  · change (componentMatching P Q active hG _ _ _).val x=_
    rw [componentMatching_outside P Q active hG _ _ _ hx,phase_unchanged_outside P Q active hx]
theorem stageMatching_companion {s : ColumnState (cutEndpoints P Q active hG)}
    (h : LocalRoutes.HasCompanion (sourceState P Q active hG) (targetState P Q active hG) s 6) :
    HasPartnerCompanion P Q (stageMatching P Q hG active s) 30 :=
  componentMatching_hasCompanion P Q active hG (partnerPhase P Q active.val) (partnerPhase Q P active.val)
    (partnerPhase_preserves_region P Q active active.val) (complementPhase_preserves_region P Q active active.val)
    (fun x _ => by simpa only [Finset.ext_iff,Finset.mem_insert,Finset.mem_singleton]
      using partnerPhase_complement P Q active.val x) h
end HiddenCircuits.Approximation.QuasimonotoneProof
