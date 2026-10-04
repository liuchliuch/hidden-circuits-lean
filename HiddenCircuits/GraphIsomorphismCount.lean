import HiddenCircuits.PerfectPartners

namespace HiddenCircuits

/-- Transport a total actual partner involution across a genuine graph isomorphism. -/
def transportPerfectPartner {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (p : PerfectPartner G) : PerfectPartner H := by
  refine ⟨fun w => e (p.val (e.symm w)),?_,?_⟩
  · intro w
    simp only [e.symm_apply_apply]
    exact (congrArg e (p.property.1 (e.symm w))).trans (e.apply_symm_apply w)
  · intro w
    have hh := e.map_rel_iff.mpr (p.property.2 (e.symm w))
    simpa only [e.apply_symm_apply] using hh

 theorem transportPerfectPartner_inverse {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (p : PerfectPartner G) :
    transportPerfectPartner e.symm (transportPerfectPartner e p)=p := by
  apply Subtype.ext
  funext v
  simp only [transportPerfectPartner,RelIso.symm_symm,e.symm_apply_apply]

/-- Actual perfect matchings are preserved bijectively by graph isomorphism. -/
noncomputable def perfectMatchingIsoEquiv {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : PerfectMatching G ≃ PerfectMatching H :=
  (perfectPartnerEquiv G).trans (({
    toFun := transportPerfectPartner e
    invFun := transportPerfectPartner e.symm
    left_inv := transportPerfectPartner_inverse e
    right_inv := transportPerfectPartner_inverse e.symm } : PerfectPartner G ≃ PerfectPartner H).trans
      (perfectPartnerEquiv H).symm)

 theorem perfectMatchingCount_congr {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    perfectMatchingCount G=perfectMatchingCount H := Fintype.card_congr (perfectMatchingIsoEquiv e)

end HiddenCircuits
