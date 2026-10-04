import HiddenCircuits.Approximation.Quasimonotone.CutRegion
import HiddenCircuits.Approximation.Quasimonotone.PartnerCompanions
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open GraphReduction CanonicalPaths FiniteChains.MonotoneSwitch
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}
  (P Q : PerfectPartner G) (base : V) (hG : Quasimonotone G)
theorem sourceState_column (i : Fin (Fintype.card (LeftSide P Q base))) :
    (cutRows P Q base hG ((sourceState P Q base hG).val i)).val =
      P.val (cutColumns P Q base hG i).val := by
  have h := cutStateEquiv_symm_apply P Q base hG (sourceState P Q base hG) (cutColumns P Q base hG i)
  simp only [Equiv.symm_apply_apply,sourceState,Equiv.apply_symm_apply] at h
  exact congrArg Subtype.val h.symm
theorem targetState_column (i : Fin (Fintype.card (LeftSide P Q base))) :
    (cutRows P Q base hG ((targetState P Q base hG).val i)).val =
      Q.val (cutColumns P Q base hG i).val := by
  have h := cutStateEquiv_symm_apply P Q base hG (targetState P Q base hG) (cutColumns P Q base hG i)
  simp only [Equiv.symm_apply_apply,targetState,Equiv.apply_symm_apply] at h
  exact congrArg Subtype.val h.symm
theorem componentMatching_column (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    (s : ColumnState (cutEndpoints P Q base hG)) (i : Fin (Fintype.card (LeftSide P Q base))) :
    (componentMatching P Q base hG B hB s).val (cutColumns P Q base hG i).val=
      (cutRows P Q base hG (s.val i)).val := by
  rw [componentMatching_right,cutStateEquiv_symm_apply,Equiv.symm_apply_apply]
theorem componentMatching_left_mem (B : PerfectPartner G) (hB : Preserves (componentRegion P Q base) B)
    (s : ColumnState (cutEndpoints P Q base hG)) {x : V} (hx : x∈LeftSide P Q base) :
    (componentMatching P Q base hG B hB s).val x∈RightSide P Q base := by
  rw [componentMatching_left P Q base hG B hB s ⟨x,hx⟩]
  exact ((cutStateEquiv P Q base hG s).val ⟨x,hx⟩).property
noncomputable def badColumns (S : Finset (Fin (Fintype.card (LeftSide P Q base)))) : Finset V :=
  S.image (fun i => (cutColumns P Q base hG i).val)
theorem right_profile (B C : PerfectPartner G)
    (hB : Preserves (componentRegion P Q base) B) (hC : Preserves (componentRegion P Q base) C)
    (s w : ColumnState (cutEndpoints P Q base hG))
    (S : Finset (Fin (Fintype.card (LeftSide P Q base))))
    (h : ∀ i,i∉S → ({s.val i,w.val i} : Finset _)={(sourceState P Q base hG).val i,(targetState P Q base hG).val i})
    (x : RightSide P Q base) (hx : x.val∉badColumns P Q base hG S) :
    ({(componentMatching P Q base hG B hB s).val x.val,
      (componentMatching P Q base hG C hC w).val x.val} : Finset V)={P.val x.val,Q.val x.val} := by
  let i := (cutColumns P Q base hG).symm x
  have hi : i∉S := by
    intro hi
    exact hx (Finset.mem_image.mpr ⟨i,hi,congrArg Subtype.val ((cutColumns P Q base hG).apply_symm_apply x)⟩)
  have hh := congrArg (fun A : Finset (Fin (Fintype.card (LeftSide P Q base))) =>
    A.image (fun j => (cutRows P Q base hG j).val)) (h i hi)
  simp only [Finset.image_insert,Finset.image_singleton,sourceState_column,targetState_column] at hh
  have he : (cutColumns P Q base hG i).val=x.val := congrArg Subtype.val ((cutColumns P Q base hG).apply_symm_apply x)
  rw [← he,componentMatching_column,componentMatching_column]
  exact hh
theorem componentMatching_hasCompanion (B C : PerfectPartner G)
    (hB : Preserves (componentRegion P Q base) B) (hC : Preserves (componentRegion P Q base) C)
    (hout : ∀x,x∉componentRegion P Q base → ({B.val x,C.val x} : Finset V)={P.val x,Q.val x})
    {s : ColumnState (cutEndpoints P Q base hG)} {d : ℕ}
    (h : LocalRoutes.HasCompanion (sourceState P Q base hG) (targetState P Q base hG) s d) :
    HasPartnerCompanion P Q (componentMatching P Q base hG B hB s) (5*d) := by
  obtain ⟨w,S,hS,h⟩ := h
  let Z := componentMatching P Q base hG B hB s
  let W := componentMatching P Q base hG C hC w
  let T := badColumns P Q base hG S
  refine ⟨W,profileExceptions P Q Z W T,?_,?_⟩
  · exact (profileExceptions_card P Q Z W T).trans
      (Nat.mul_le_mul_left 5 ((Finset.card_image_le).trans hS))
  · intro x hx
    have he := outside_profileExceptions P Q Z W T hx
    by_cases hr : x∈RightSide P Q base
    · exact right_profile P Q base hG B C hB hC s w S h ⟨x,hr⟩ he.1
    by_cases hl : x∈LeftSide P Q base
    · have hZ := componentMatching_left_mem P Q base hG B hB s hl
      have hW := componentMatching_left_mem P Q base hG C hC w hl
      have hP := p_left_to_right (partnerPerm P) (partnerPerm Q) base hl
      have hQ := q_left_to_right (partnerPerm P) (partnerPerm Q) (partnerPerm_involutive P) (partnerPerm_involutive Q) base hl
      apply profile_of_neighbor_profiles P Q Z W x
      · exact right_profile P Q base hG B C hB hC s w S h ⟨Z.val x,hZ⟩ he.2.2.2.1
      · exact right_profile P Q base hG B C hB hC s w S h ⟨W.val x,hW⟩ he.2.2.2.2
      · exact right_profile P Q base hG B C hB hC s w S h ⟨P.val x,hP⟩ he.2.1
      · exact right_profile P Q base hG B C hB hC s w S h ⟨Q.val x,hQ⟩ he.2.2.1
    · have hu : x∉componentRegion P Q base := by simpa only [componentRegion,Set.mem_union,not_or] using And.intro hl hr
      change ({(componentMatching P Q base hG B hB s).val x,(componentMatching P Q base hG C hC w).val x} : Finset V)=_
      rw [componentMatching_outside P Q base hG B hB s hu,componentMatching_outside P Q base hG C hC w hu]
      exact hout x hu
end HiddenCircuits.Approximation.QuasimonotoneProof
