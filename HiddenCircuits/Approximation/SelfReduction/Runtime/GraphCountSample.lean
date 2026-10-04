import HiddenCircuits.Approximation.SamplerRuntime.GraphPadding
import HiddenCircuits.Approximation.SelfReduction.MatchingFibers
import HiddenCircuits.Approximation.SelfReduction.Runtime.FirstPartnerTotal
import HiddenCircuits.Approximation.SelfReduction.Runtime.StatisticalBridge

/-! The actual initialized graph sampler's observed first partner. All-event
bias is against the genuine matching-deletion fiber, with failure unconditioned. -/
namespace HiddenCircuits.Approximation.SelfReduction.GraphCountSample
open Complexity GraphReduction SamplerRuntime Runtime
attribute [local instance] Classical.propDecidable

noncomputable def sampled {n : ℕ} (G : MatrixGraph n) (N : ℕ) (coins : BitString) :
    Option (PerfectPartner G.graph) :=
  (Initialization.RawExtraction.initialPartner G N (TapeRead.takePadded (3*N^4) coins)).map
    (fun P => PartnerIteration.iterate G (PartnerBudget.steps N) P (coins.drop (3*N^4)))

lemma core_bytes {n : ℕ} (G : MatrixGraph n) (N : ℕ) (coins : BitString) :
    GraphFunctional.core G N coins=match sampled G N coins with
      | none => [] | some P => PartnerOutput.success G P := by
  unfold GraphFunctional.core sampled PartnerRunner.afterInitialize
  cases Initialization.RawExtraction.initialPartner G N (TapeRead.takePadded (3*N^4) coins) <;> rfl

def partner {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (P : PerfectPartner G.graph) : Fin (b+1) := ⟨(P.val 0).val,lt_of_lt_of_le (P.val 0).isLt hn⟩
noncomputable def sample {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (N : ℕ) (coins : BitString) : Option (Fin (b+1)) :=
  (sampled G N coins).map (partner G hn)

lemma firstPartner_success {n : ℕ} (G : MatrixGraph (n+1)) (P : PerfectPartner G.graph) :
    firstPartnerValue (PartnerOutput.success G P)=true::List.replicate (P.val 0).val true := by
  exact firstPartnerValue_witness (PartnerMove.partnerPermutation G P)

lemma sample_bytes {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (N : ℕ) (coins : BitString) :
    firstPartnerValue (GraphFunctional.core G N coins)=encodePartner (sample G hn N coins) := by
  rw [core_bytes]
  cases hs:sampled G N coins with
  | none => simp [sample,hs,encodePartner]
  | some P => simp [sample,hs,encodePartner,firstPartner_success,partner]

def partnerEvent {b : ℕ} (j : Fin (b+1)) : Option BitString → Prop
  | none => False
  | some w => firstPartnerValue (true::w)=encodePartner (some j)

lemma partnerEvent_success {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (P : PerfectPartner G.graph) (j : Fin (b+1)) :
    partnerEvent j (some (PartnerOutput.witness G P)) ↔ partner G hn P=j := by
  change firstPartnerValue (PartnerOutput.success G P)=encodePartner (some j) ↔ _
  rw [firstPartner_success]
  change encodePartner (some (partner G hn P))=encodePartner (some j) ↔ _
  rw [(encodePartner_injective b).eq_iff,Option.some.injEq]

lemma sample_event {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (N : ℕ) (coins : BitString) (j : Fin (b+1)) :
    partnerEvent j (decodeSample (GraphFunctional.core G N coins)) ↔ sample G hn N coins=some j := by
  rw [core_bytes]
  cases hs:sampled G N coins with
  | none => simp [sample,hs,partnerEvent,decodeSample]
  | some P =>
    simp only [sample,hs,Option.map_some,Option.some.injEq,PartnerOutput.decode_success]
    exact partnerEvent_success G hn P j

noncomputable def childCount {b n : ℕ} (G : MatrixGraph (n+1)) (j : Fin (b+1)) : ℕ :=
  if hj:j.val < n+1 then matchingChildCount G.graph 0 ⟨j.val,hj⟩ else 0

lemma partner_card {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1) (j : Fin (b+1)) :
    Fintype.card {P : PerfectPartner G.graph // partner G hn P=j}=childCount G j := by
  classical
  unfold childCount
  split_ifs with hj
  · rw [matchingChildCount_eq_fiber]
    let e : {P : PerfectPartner G.graph // partner G hn P=j} ≃ EdgeFiber G.graph 0 ⟨j.val,hj⟩ :=
      Equiv.subtypeEquivRight (fun P => by simp [partner,Fin.ext_iff])
    simp only [Fintype.card_eq_nat_card]
    exact Nat.card_congr e
  · letI : IsEmpty {P : PerfectPartner G.graph // partner G hn P=j} := ⟨fun P => by
      have he:=congrArg Fin.val P.property
      exact hj (he ▸ (P.val.val 0).isLt)⟩
    exact Fintype.card_eq_zero

lemma uniform_partner {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (P : PerfectPartner G.graph) (j : Fin (b+1)) :
    uniformProbability (PartnerOutput.witnesses G) (partnerEvent j)=
      (childCount G j:ℚ)/perfectMatchingCount G.graph := by
  rw [PartnerOutput.uniform_witnesses G P]
  have he:=Fintype.card_congr (Equiv.subtypeEquivRight (fun Q => partnerEvent_success G hn Q j))
  rw [he,partner_card,perfectMatchingCount_eq_partners]

/-- Uniformly padded finite fair tapes satisfy the exact first-partner ratio.
The only graph hypothesis is the mathematical quasimonotone promise. -/
theorem bias {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (hG : Quasimonotone G.graph) (N k m : ℕ) (hN : n+1 ≤ N) (hk : k+1 ≤ N)
    (hm : 3*N^4+PartnerBudget.bits N ≤ m) (hc : 0 < perfectMatchingCount G.graph) (j : Fin (b+1)) :
    |coinProbability m (fun r => sample G hn N (List.ofFn r)=some j)-
      (childCount G j:ℚ)/perfectMatchingCount G.graph| ≤ 1/(2^k:ℚ) := by
  rw [perfectMatchingCount_eq_partners] at hc
  obtain ⟨P⟩:=Fintype.card_pos_iff.mp hc
  have hh:=GraphPadding.core_event_error G hG N k m hN hk hm (partnerEvent j)
  rw [uniform_partner G hn P j] at hh
  have he:=coinProbability_congr (m:=m) (fun r => sample_event G hn N (List.ofFn r) j)
  rw [he] at hh
  exact hh

lemma sample_sound {b n : ℕ} (G : MatrixGraph (n+1)) (hn : n+1 ≤ b+1)
    (N : ℕ) (coins : BitString) (j : Fin (b+1)) (h:sample G hn N coins=some j) :
    0 < childCount G j := by
  obtain ⟨P,hP,hj⟩:=Option.map_eq_some_iff.mp h
  rw [←partner_card G hn j]
  exact Fintype.card_pos_iff.mpr ⟨P,hj⟩
end HiddenCircuits.Approximation.SelfReduction.GraphCountSample
