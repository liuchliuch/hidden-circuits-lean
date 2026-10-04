import HiddenCircuits.Approximation.Quasimonotone.CutCoordinates
import HiddenCircuits.Approximation.Quasimonotone.RegionSplice
import HiddenCircuits.Approximation.Quasimonotone.PartnerReconstruction
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open GraphReduction CanonicalPaths FiniteChains.MonotoneSwitch
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}
  (P Q : PerfectPartner G) (base : V)
abbrev componentRegion : Set V := LeftSide P Q base ∪ RightSide P Q base
theorem mem_componentRegion (x : V) : x∈componentRegion P Q base ↔ (matchingUnion P Q).Reachable base x :=
  (reachable_iff_orbits _ _ (partnerPerm_involutive P) (partnerPerm_involutive Q)
    (partnerPerm_free P) (partnerPerm_free Q) base x).symm
theorem source_preserves_region : Preserves (componentRegion P Q base) P := by
  intro x
  rw [mem_componentRegion,mem_componentRegion]
  have h : (matchingUnion P Q).Reachable x (P.val x) := SimpleGraph.Adj.reachable (Or.inl rfl)
  exact ⟨fun hh => hh.trans h,fun hh => hh.trans h.symm⟩
theorem target_preserves_region : Preserves (componentRegion P Q base) Q := by
  intro x
  rw [mem_componentRegion,mem_componentRegion]
  have h : (matchingUnion P Q).Reachable x (Q.val x) := SimpleGraph.Adj.reachable (Or.inr rfl)
  exact ⟨fun hh => hh.trans h,fun hh => hh.trans h.symm⟩
theorem extendCut_preserves_region (f : ComponentCut P Q base) :
    Preserves (componentRegion P Q base) (extendCut P Q base f) := by
  have hm : ∀ x∈componentRegion P Q base,(extendCut P Q base f).val x∈componentRegion P Q base := by
    intro x hx
    rcases hx with hl|hr
    · change extendCutFun P Q base f x∈componentRegion P Q base
      rw [extendCut_left P Q base f ⟨x,hl⟩]
      exact Or.inr (f.val ⟨x,hl⟩).property
    · change extendCutFun P Q base f x∈componentRegion P Q base
      rw [extendCut_right P Q base f ⟨x,hr⟩]
      exact Or.inl (f.val.symm ⟨x,hr⟩).property
  intro x
  exact ⟨hm x,fun h => by simpa only [(extendCut P Q base f).property.1 x] using hm _ h⟩
variable (hG : Quasimonotone G)
noncomputable def componentMatching (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    (s : ColumnState (cutEndpoints P Q base hG)) : PerfectPartner G :=
  splice (componentRegion P Q base) (cutMatching P Q base hG s) B
    (extendCut_preserves_region P Q base _) hB
theorem componentMatching_inside (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    (s : ColumnState (cutEndpoints P Q base hG)) {x : V} (hx : x∈componentRegion P Q base) :
    (componentMatching P Q base hG B hB s).val x=(cutMatching P Q base hG s).val x :=
  splice_inside _ _ _ _ _ hx
theorem componentMatching_outside (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    (s : ColumnState (cutEndpoints P Q base hG)) {x : V} (hx : x∉componentRegion P Q base) :
    (componentMatching P Q base hG B hB s).val x=B.val x :=
  splice_outside _ _ _ _ _ hx
theorem componentMatching_left (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    (s : ColumnState (cutEndpoints P Q base hG)) (x : LeftSide P Q base) :
    (componentMatching P Q base hG B hB s).val x.val=
      ((cutStateEquiv P Q base hG s).val x).val := by
  rw [componentMatching_inside P Q base hG B hB s (Or.inl x.property)]
  exact extendCut_left P Q base _ x
theorem componentMatching_right (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    (s : ColumnState (cutEndpoints P Q base hG)) (x : RightSide P Q base) :
    (componentMatching P Q base hG B hB s).val x.val=
      ((cutStateEquiv P Q base hG s).val.symm x).val := by
  rw [componentMatching_inside P Q base hG B hB s (Or.inr x.property)]
  exact extendCut_right P Q base _ x
theorem componentMatching_move (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    {s t : ColumnState (cutEndpoints P Q base hG)} (hm : LocalRoutes.Move Finset.univ s t) :
    PartnerMove (componentMatching P Q base hG B hB s) (componentMatching P Q base hG B hB t) := by
  obtain ⟨i,_,j,_,h⟩ := hm
  let a := cutColumns P Q base hG i
  let b := cutColumns P Q base hG j
  refine ⟨a.val,b.val,?_⟩
  exact splice_conjugate _ _ _ _ _ _ _ a.val b.val (Or.inr a.property) (Or.inr b.property)
    (extendCut_conjugate P Q base _ _ a b (cutStateEquiv_transpose P Q base hG i j h))
end HiddenCircuits.Approximation.QuasimonotoneProof
