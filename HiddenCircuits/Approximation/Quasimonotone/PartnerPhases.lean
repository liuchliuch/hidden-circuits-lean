import HiddenCircuits.Approximation.Quasimonotone.PartnerReconstruction
import HiddenCircuits.Approximation.Quasimonotone.RegionSplice
namespace HiddenCircuits.Approximation.QuasimonotoneProof
open CanonicalPaths.UnionReconstruction
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {G : SimpleGraph (Fin n)}
noncomputable def partnerComponentVertices (p q : PerfectPartner G) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (matchingUnion p q).Reachable i j)
theorem partnerComponentVertices_nonempty (p q : PerfectPartner G) (i : Fin n) :
    (partnerComponentVertices p q i).Nonempty := by
  refine ⟨i,?_⟩
  simp [partnerComponentVertices,SimpleGraph.Reachable.refl]
noncomputable def partnerComponentMin (p q : PerfectPartner G) (i : Fin n) : Fin n :=
  (partnerComponentVertices p q i).min' (partnerComponentVertices_nonempty p q i)
theorem partnerComponentMin_reachable (p q : PerfectPartner G) (i : Fin n) :
    (matchingUnion p q).Reachable (partnerComponentMin p q i) i := by
  have h := Finset.min'_mem (partnerComponentVertices p q i) (partnerComponentVertices_nonempty p q i)
  simp only [partnerComponentVertices,Finset.mem_filter,Finset.mem_univ,true_and] at h
  exact h.symm
theorem partnerComponentMin_eq_of_reachable {p q : PerfectPartner G} {i j : Fin n}
    (h : (matchingUnion p q).Reachable i j) : partnerComponentMin p q i=partnerComponentMin p q j := by
  have hs : partnerComponentVertices p q i=partnerComponentVertices p q j := by
    ext v
    simp only [partnerComponentVertices,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun hv => h.symm.trans hv,fun hv => h.trans hv⟩
  unfold partnerComponentMin
  simp only [hs]
theorem partnerComponentMin_sameUnion {p q r s : PerfectPartner G} (h : SamePartnerUnion p q r s)
    (i : Fin n) : partnerComponentMin p q i=partnerComponentMin r s i := by
  have hs : partnerComponentVertices p q i=partnerComponentVertices r s i := by
    unfold partnerComponentVertices
    rw [matchingUnion_eq h]
  unfold partnerComponentMin
  simp only [hs]
noncomputable def partnerPhaseValue (P Q : PerfectPartner G) (cut : ℕ) (x : Fin n) : Fin n :=
  if (partnerComponentMin P Q x).val < cut then Q.val x else P.val x

theorem partnerComponentMin_source (P Q : PerfectPartner G) (x : Fin n) :
    partnerComponentMin P Q x=partnerComponentMin P Q (P.val x) :=
  partnerComponentMin_eq_of_reachable (SimpleGraph.Adj.reachable (Or.inl rfl))

theorem partnerComponentMin_target (P Q : PerfectPartner G) (x : Fin n) :
    partnerComponentMin P Q x=partnerComponentMin P Q (Q.val x) :=
  partnerComponentMin_eq_of_reachable (SimpleGraph.Adj.reachable (Or.inr rfl))

noncomputable def partnerPhase (P Q : PerfectPartner G) (cut : ℕ) : PerfectPartner G := by
  refine ⟨partnerPhaseValue P Q cut,?_,?_⟩
  · intro x
    by_cases hx : (partnerComponentMin P Q x).val < cut
    · simp only [partnerPhaseValue,if_pos hx,← partnerComponentMin_target P Q x,Q.property.1 x]
    · simp only [partnerPhaseValue,if_neg hx,← partnerComponentMin_source P Q x,P.property.1 x]
  · intro x
    unfold partnerPhaseValue
    split_ifs
    · exact Q.property.2 x
    · exact P.property.2 x

@[simp] theorem partnerPhase_zero (P Q : PerfectPartner G) : partnerPhase P Q 0=P := by
  apply Subtype.ext
  funext x
  simp [partnerPhase,partnerPhaseValue]

@[simp] theorem partnerPhase_full (P Q : PerfectPartner G) : partnerPhase P Q n=Q := by
  apply Subtype.ext
  funext x
  simp [partnerPhase,partnerPhaseValue,(partnerComponentMin P Q x).isLt]

def PartnerInterrupted (P Q Z : PerfectPartner G) (active : Fin n) : Prop :=
  ∀ x, ¬(matchingUnion P Q).Reachable active x → Z.val x=(partnerPhase P Q active.val).val x

theorem partner_reconstruct_interrupted {P Q R S Z : PerfectPartner G} {active : Fin n}
    (hU : SamePartnerUnion P Q R S) (hp : PartnerInterrupted P Q Z active)
    (hr : PartnerInterrupted R S Z active) (horient : R.val active=P.val active) : P=R ∧ Q=S := by
  have hall : ∀ x,R.val x=P.val x := by
    intro x
    by_cases hx : (matchingUnion P Q).Reachable active x
    · exact partner_left_eq_of_reachable hU hx horient
    have hx' : ¬(matchingUnion R S).Reachable active x := by rwa [← matchingUnion_eq hU]
    have h₁ := hp x hx
    have h₂ := hr x hx'
    change Z.val x=partnerPhaseValue P Q active.val x at h₁
    change Z.val x=partnerPhaseValue R S active.val x at h₂
    have hm := partnerComponentMin_sameUnion hU x
    unfold partnerPhaseValue at h₁ h₂
    rw [← hm] at h₂
    by_cases hc : (partnerComponentMin P Q x).val < active.val
    · simp only [if_pos hc] at h₁ h₂
      exact left_eq_of_right_eq hU (h₂.symm.trans h₁)
    · simp only [if_neg hc] at h₁ h₂
      exact h₂.symm.trans h₁
  constructor
  · exact Subtype.ext (funext fun x => (hall x).symm)
  · exact Subtype.ext (funext fun x => (right_eq_of_left_eq hU (hall x)).symm)

end HiddenCircuits.Approximation.QuasimonotoneProof
