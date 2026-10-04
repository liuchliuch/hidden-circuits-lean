import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualReduction
import HiddenCircuits.Approximation.SelfReduction.Runtime.PartnerBatch
import HiddenCircuits.Approximation.SelfReduction.Runtime.StatisticalBridge
import HiddenCircuits.Approximation.SamplerRuntime.MonotonePadding

/-! Exact typed branch experiment for the literal initialized endpoint sampler.
It keeps failure, embeds partners into the original fixed branch cap, and
transfers the actual padded fair-tape event bound to residual count ratios. -/
namespace HiddenCircuits.Approximation.SelfReduction.EndpointResidual
open Complexity GraphReduction SamplerRuntime Runtime
open GraphReduction.MonotoneEndpointEncoding
attribute [local instance] Classical.propDecidable

/-- The observed column index is embedded in the original candidate range. -/
def partner {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1) (P : E.Permutations) : Fin (b+1) :=
  ⟨(P.val 0).val,lt_of_lt_of_le (P.val 0).isLt hE⟩

def activeSample {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (k : ℕ) (coins : BitString) : Option (Fin (b+1)) :=
  match E.startingPermutation with
  | none => none
  | some P => some (partner E hE (Iteration.iterate E (Budget.steps (sampleInput (encode ⟨d+1,E⟩) k).length) P coins))

def sample {b : ℕ} (k m : ℕ) : State b  →  CoinTape m  →  Option (Fin (b+1))
  | ⟨0,_⟩,_ => none
  | ⟨d+1,none⟩,_ => none
  | ⟨d+1,some E⟩,r => activeSample E.val E.property k (List.ofFn r)

/-- Pointwise semantic equality with the bytes produced by the fixed actual
sampler and first-partner decoder, including initialization failure. -/
theorem activeSample_bytes {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (k : ℕ) (coins : BitString) :
    partnerEvaluate (pairBits (sampleInput (encode ⟨d+1,E⟩) k) coins)=encodePartner (activeSample E hE k coins) := by
  unfold partnerEvaluate
  rw [Functional.evaluate_canonical]
  cases hs : E.startingPermutation with
  | none => simp [Core.evaluate,activeSample,hs,encodePartner]
  | some P => simp only [Core.evaluate,activeSample,hs,firstPartnerValue_witness,encodePartner,partner]

def partnerEvent {b : ℕ} (j : Fin (b+1)) : Option BitString  →  Prop
  | none => False
  | some w => firstPartnerValue (true::w)=encodePartner (some j)

lemma partnerEvent_witness {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (P : E.Permutations) (j : Fin (b+1)) :
    partnerEvent j (some (Output.witness P.val)) ↔ partner E hE P=j := by
  change firstPartnerValue (Output.success P.val)=encodePartner (some j) ↔ _
  rw [firstPartnerValue_witness]
  change encodePartner (some (partner E hE P))=encodePartner (some j) ↔ _
  rw [(encodePartner_injective b).eq_iff,Option.some.injEq]

lemma activeSample_event {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (k : ℕ) (coins : BitString) (j : Fin (b+1)) :
    partnerEvent j (decodeSample (Functional.evaluate (pairBits (sampleInput (encode ⟨d+1,E⟩) k) coins))) ↔
      activeSample E hE k coins=some j := by
  rw [Functional.evaluate_canonical]
  cases hs : E.startingPermutation with
  | none => simp [Core.evaluate,activeSample,hs,partnerEvent,decodeSample]
  | some P =>
    simp only [Core.evaluate,activeSample,hs,Output.decode_success,Option.some.injEq]
    exact partnerEvent_witness E hE _ j

/-- Every padded branch fiber is exactly the corresponding typed child count. -/
theorem partner_card {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1) (j : Fin (b+1)) :
    Fintype.card {P : E.Permutations // partner E hE P=j}=count (child ⟨d+1,some ⟨E,hE⟩⟩ j) := by
  rw [child_count]
  by_cases hj : j.val<d+1
  · rw [dif_pos hj]
    have he : {P : E.Permutations // partner E hE P=j} ≃ EndpointFiber.Fiber E ⟨j.val,hj⟩ :=
      Equiv.subtypeEquivRight (fun P => by simp [partner,Fin.ext_iff])
    rw [Fintype.card_congr he]
    by_cases ha : E.lo 0  ≤  j.val ∧ j.val<E.hi 0
    · rw [if_pos ha,EndpointFiber.card_fiber E ⟨j.val,hj⟩ ha]
    · rw [if_neg ha,EndpointFiber.card_fiber_zero E ⟨j.val,hj⟩ ha]
  · rw [dif_neg hj]
    letI : IsEmpty {P : E.Permutations // partner E hE P=j} := ⟨fun P => by
      have he := congrArg Fin.val P.property
      exact hj (he ▸ (P.val.val 0).isLt)⟩
    exact Fintype.card_eq_zero

lemma uniform_partner {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (P : E.Permutations) (j : Fin (b+1)) :
    uniformProbability (Output.witnesses E) (partnerEvent j)=
      (reduction b).branchProbability ⟨d+1,some ⟨E,hE⟩⟩ j := by
  rw [Output.uniform_witnesses E P]
  have he : Fintype.card {Q : E.Permutations // partnerEvent j (some (Output.witness Q.val))}=
      Fintype.card {Q : E.Permutations // partner E hE Q=j} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun Q => partnerEvent_witness E hE Q j))
  rw [he,partner_card]
  rfl

/-- Bias of the actual initialized, padded-tape branch sampler is bounded by
its unconditional all-events sampler error, against the exact residual ratio. -/
theorem activeSample_bias {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (k m : ℕ) (hm : Budget.bits (sampleInput (encode ⟨d+1,E⟩) k).length  ≤  m)
    (hc : 0<Fintype.card E.Permutations) (j : Fin (b+1)) :
    |coinProbability m (fun r => activeSample E hE k (List.ofFn r)=some j)-
      (reduction b).branchProbability ⟨d+1,some ⟨E,hE⟩⟩ j|  ≤  1/(2^k:ℚ) := by
  obtain ⟨P⟩ := Fintype.card_pos_iff.mp hc
  have h := MonotonePadding.event_error ⟨d+1,E⟩ k m hm (partnerEvent j)
  rw [Output.solutions_encode,uniform_partner E hE P j] at h
  have he := coinProbability_congr (m:=m) (fun r => activeSample_event E hE k (List.ofFn r) j)
  rw [he] at h
  exact h

/-- An observed successful sample has a positive active child on every tape. -/
theorem activeSample_sound {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (k : ℕ) (coins : BitString) (j : Fin (b+1)) (h : activeSample E hE k coins=some j) :
    0<count (child ⟨d+1,some ⟨E,hE⟩⟩ j) := by
  cases hs : E.startingPermutation with
  | none => simp [activeSample,hs] at h
  | some P =>
    have he : partner E hE (Iteration.iterate E (Budget.steps (sampleInput (encode ⟨d+1,E⟩) k).length) P coins)=j := by
      simpa [activeSample,hs] using h
    rw [←he]
    exact observed_child_positive E hE _

/-- The physical partner bytes match the state-indexed branch sampler on every
coin tape, not only on the high-probability successful event. -/
theorem sample_active_bytes {b d : ℕ} (E : MonotoneEndpoints (d+1)) (hE : d+1  ≤  b+1)
    (k m : ℕ) (r : CoinTape m) :
    partnerEvaluate (pairBits (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨E,hE⟩⟩) k) (List.ofFn r))=
      encodePartner (sample k m ⟨d+1,some ⟨E,hE⟩⟩ r) := activeSample_bytes E hE k (List.ofFn r)

/-- State-indexed all-tape soundness needed for early-zero counting control. -/
theorem sample_sound {b : ℕ} (k m : ℕ) (s : State b) (r : CoinTape m) (j : Fin (b+1))
    (h : sample k m s r=some j) : 0<count (child s j) := by
  rcases s with ⟨d,E⟩
  cases d with
  | zero => simp [sample] at h
  | succ d =>
    cases E with
    | none => simp [sample] at h
    | some E => exact activeSample_sound E.val E.property k (List.ofFn r) j h

/-- One shared padded tape length supports the exact CountReduction branch
bias hypotheses for every nonempty positive-rank canonical residual. -/
theorem sample_bias {b : ℕ} (k m : ℕ)
    (hm : ∀d,∀E : MonotoneEndpoints (d+1),d+1  ≤  b+1  →  
      Budget.bits (sampleInput (encode ⟨d+1,E⟩) k).length  ≤  m)
    (s : State b) (hc : 0<count s) (hr : 0<rank s) (j : Fin (b+1)) :
    |coinProbability m (fun r => sample k m s r=some j)-(reduction b).branchProbability s j|  ≤  1/(2^k:ℚ) := by
  rcases s with ⟨d,E⟩
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 hr)
  | succ d =>
    cases E with
    | none => exact False.elim (Nat.lt_irrefl 0 hc)
    | some E => exact activeSample_bias E.val E.property k m (hm d E.val E.property) hc j

end HiddenCircuits.Approximation.SelfReduction.EndpointResidual
