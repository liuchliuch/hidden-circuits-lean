import HiddenCircuits.PerfectPartners

/-! Removing exactly the unmatched vertices gives an actual perfect matching of
an induced graph, with explicit inverse restriction and extension maps. -/
namespace HiddenCircuits

/-- A partial graph matching that covers exactly the specified retained vertex set. -/
def ExactMatching {V : Type*} (G : SimpleGraph V) (A : Set V) :=
  {m : EncodedMatching G // ∀ v, m.val v = none ↔ v ∉ A}

namespace ExactMatching
variable {V : Type*} {G : SimpleGraph V} {A : Set V}

 theorem exists_partner (m : ExactMatching G A) (v : A) :
    ∃ w : A, m.val.val v.val = some w.val := by
  have hn : m.val.val v.val ≠ none := fun h => ((m.property v.val).mp h) v.property
  obtain ⟨w,hw⟩ := Option.ne_none_iff_exists'.mp hn
  have hback := m.val.property.1 v.val w hw
  have hwa : w ∈ A := by
    by_contra hwa
    have hz := (m.property w).mpr hwa
    rw [hz] at hback
    contradiction
  exact ⟨⟨w,hwa⟩,hw⟩

noncomputable def partner (m : ExactMatching G A) (v : A) : A :=
  (m.exists_partner v).choose

 theorem partner_spec (m : ExactMatching G A) (v : A) :
    m.val.val v.val = some (m.partner v).val := (m.exists_partner v).choose_spec

noncomputable def toPartner (m : ExactMatching G A) : PerfectPartner (G.induce A) := by
  refine ⟨m.partner,?_,?_⟩
  · intro v
    apply Subtype.ext
    apply Option.some.inj
    exact (m.partner_spec (m.partner v)).symm.trans
      (m.val.property.1 v.val (m.partner v).val (m.partner_spec v))
  · intro v
    exact m.val.property.2 v.val (m.partner v).val (m.partner_spec v)
end ExactMatching

namespace PerfectPartner
variable {V : Type*} {G : SimpleGraph V} {A : Set V}

noncomputable def extendPartner (p : PerfectPartner (G.induce A)) (v : V) : Option V := by
  classical
  exact if hv : v ∈ A then some (p.val ⟨v,hv⟩).val else none

noncomputable def extendMatching (p : PerfectPartner (G.induce A)) : EncodedMatching G := by
  classical
  refine ⟨p.extendPartner,?_,?_⟩
  · intro v w h
    unfold extendPartner at h ⊢
    split_ifs at h with hv
    have he : (p.val ⟨v,hv⟩).val = w := Option.some.inj h
    have hw : w ∈ A := he ▸ (p.val ⟨v,hv⟩).property
    rw [dif_pos hw]
    congr 1
    have hes : p.val ⟨v,hv⟩ = ⟨w,hw⟩ := Subtype.ext he
    have hh := p.property.1 ⟨v,hv⟩
    rw [hes] at hh
    exact congrArg Subtype.val hh
  · intro v w h
    unfold extendPartner at h
    split_ifs at h with hv
    have he : (p.val ⟨v,hv⟩).val = w := Option.some.inj h
    rw [← he]
    exact p.property.2 ⟨v,hv⟩

noncomputable def toExactMatching (p : PerfectPartner (G.induce A)) : ExactMatching G A := by
  classical
  refine ⟨p.extendMatching,?_⟩
  intro v
  change (if hv : v ∈ A then some (p.val ⟨v,hv⟩).val else none) = none ↔ v ∉ A
  by_cases hv : v ∈ A <;> simp [hv]

 theorem toExactMatching_toPartner (p : PerfectPartner (G.induce A)) :
    p.toExactMatching.toPartner = p := by
  apply Subtype.ext
  funext v
  apply Subtype.ext
  have h := p.toExactMatching.partner_spec v
  change p.extendPartner v.val = some (p.toExactMatching.partner v).val at h
  unfold extendPartner at h
  rw [dif_pos v.property] at h
  exact (Option.some.inj h).symm
end PerfectPartner

 theorem ExactMatching.toPartner_toExactMatching {V : Type*} {G : SimpleGraph V} {A : Set V}
    (m : ExactMatching G A) : m.toPartner.toExactMatching = m := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  funext v
  change (if hv : v ∈ A then some (m.partner ⟨v,hv⟩).val else none) = m.val.val v
  split_ifs with hv
  · exact (m.partner_spec ⟨v,hv⟩).symm
  · exact ((m.property v).mpr hv).symm

/-- Covering exactly the retained vertices is equivalent to an actual perfect
matching of the induced graph on those vertices. -/
noncomputable def exactMatchingPerfectEquiv {V : Type*} (G : SimpleGraph V) (A : Set V) :
    ExactMatching G A ≃ PerfectMatching (G.induce A) :=
  ({ toFun := ExactMatching.toPartner
     invFun := PerfectPartner.toExactMatching
     left_inv := ExactMatching.toPartner_toExactMatching
     right_inv := PerfectPartner.toExactMatching_toPartner } :
       ExactMatching G A ≃ PerfectPartner (G.induce A)).trans (perfectPartnerEquiv _).symm

end HiddenCircuits
