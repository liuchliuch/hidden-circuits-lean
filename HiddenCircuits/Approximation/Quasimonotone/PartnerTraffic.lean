import HiddenCircuits.Approximation.Quasimonotone.PartnerPhases
import HiddenCircuits.Approximation.Quasimonotone.PartnerCompanions
import HiddenCircuits.Approximation.CanonicalPaths.UnionCode
namespace HiddenCircuits.Approximation.QuasimonotoneProof.PartnerTraffic
open CanonicalPaths.UnionReconstruction
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {G : SimpleGraph (Fin n)}
abbrev Pairs (Z : PerfectPartner G) (d : ℕ) :=
  {pq : PerfectPartner G × PerfectPartner G // ∃ active : Fin n,
    PartnerInterrupted pq.1 pq.2 Z active ∧ HasPartnerCompanion pq.1 pq.2 Z d}
noncomputable def active {Z : PerfectPartner G} {d : ℕ} (t : Pairs Z d) : Fin n := t.property.choose
theorem interrupted {Z : PerfectPartner G} {d : ℕ} (t : Pairs Z d) :
    PartnerInterrupted t.val.1 t.val.2 Z (active t) := t.property.choose_spec.1
noncomputable def companion {Z : PerfectPartner G} {d : ℕ} (t : Pairs Z d) : PerfectPartner G :=
  t.property.choose_spec.2.choose
noncomputable def exceptional {Z : PerfectPartner G} {d : ℕ} (t : Pairs Z d) : Finset (Fin n) :=
  t.property.choose_spec.2.choose_spec.choose
theorem exceptional_card {Z : PerfectPartner G} {d : ℕ} (t : Pairs Z d) : (exceptional t).card ≤ d :=
  t.property.choose_spec.2.choose_spec.choose_spec.1
theorem outside {Z : PerfectPartner G} {d : ℕ} (t : Pairs Z d) :
    ∀ i,i∉exceptional t → ({t.val.1.val i,t.val.2.val i} : Set (Fin n))=
      {Z.val i,(companion t).val i} := by
  intro i hi
  have h := t.property.choose_spec.2.choose_spec.choose_spec.2 i hi
  have hh := congrArg (fun f : Finset (Fin n) => (f : Set (Fin n))) h.symm
  simpa only [Finset.coe_pair] using hh
noncomputable def encode (fallback : Fin n) {Z : PerfectPartner G} {d : ℕ} (t : Pairs Z d) :
    PerfectPartner G × RepairCode n d × Fin n × Fin n :=
  (companion t,encodeRepair fallback (partnerPerm t.val.1) (partnerPerm t.val.2)
    (exceptional t) (exceptional_card t),active t,t.val.1.val (active t))
theorem encode_injective (fallback : Fin n) (Z : PerfectPartner G) (d : ℕ) :
    Function.Injective (encode fallback : Pairs Z d → PerfectPartner G × RepairCode n d × Fin n × Fin n) := by
  intro x y h
  have hw : companion x=companion y := congrArg (fun t : PerfectPartner G × RepairCode n d × Fin n × Fin n => t.1) h
  have hc : encodeRepair fallback (partnerPerm x.val.1) (partnerPerm x.val.2) (exceptional x) (exceptional_card x)=
      encodeRepair fallback (partnerPerm y.val.1) (partnerPerm y.val.2) (exceptional y) (exceptional_card y) :=
    congrArg (fun t : PerfectPartner G × RepairCode n d × Fin n × Fin n => t.2.1) h
  have ha : active x=active y := congrArg (fun t : PerfectPartner G × RepairCode n d × Fin n × Fin n => t.2.2.1) h
  have ho : x.val.1.val (active x)=y.val.1.val (active y) :=
    congrArg (fun t : PerfectPartner G × RepairCode n d × Fin n × Fin n => t.2.2.2) h
  have hU : SamePartnerUnion x.val.1 x.val.2 y.val.1 y.val.2 :=
    sameUnion_of_equal_code fallback _ _ _ _ (partnerPerm Z) (partnerPerm (companion x))
      (exceptional x) (exceptional y) (exceptional_card x) (exceptional_card y)
      (outside x) (by simpa only [hw] using outside y) hc
  have hy : PartnerInterrupted y.val.1 y.val.2 Z (active x) := by
    simpa only [ha] using interrupted y
  have horient : y.val.1.val (active x)=x.val.1.val (active x) := by
    rw [← ha] at ho
    exact ho.symm
  have he := partner_reconstruct_interrupted hU (interrupted x) hy horient
  exact Subtype.ext (Prod.ext he.1 he.2)
theorem pairs_card_bound (Z : PerfectPartner G) (d : ℕ) :
    Fintype.card (Pairs Z d) ≤
      Fintype.card (PerfectPartner G)*((n+1)^d*n^d*n^d)*n*n := by
  by_cases hn : n=0
  · subst n
    haveI : IsEmpty (Pairs Z d) := ⟨fun t => Fin.elim0 (active t)⟩
    simp
  · let fallback : Fin n := ⟨0,Nat.pos_of_ne_zero hn⟩
    have h := Fintype.card_le_of_injective (encode fallback : Pairs Z d →
      PerfectPartner G × RepairCode n d × Fin n × Fin n) (encode_injective fallback Z d)
    simpa only [Fintype.card_prod,Fintype.card_fin,RepairCode.card,mul_assoc] using h
end HiddenCircuits.Approximation.QuasimonotoneProof.PartnerTraffic
