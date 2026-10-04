import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountReduction
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSample
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountBudget

/-! Initialized general-graph samples with explicit failure mass. -/
namespace HiddenCircuits.Approximation.SelfReduction.GraphCount
open Complexity SamplerRuntime Runtime
attribute [local instance] Classical.propDecidable

noncomputable def activeSample {b d : ℕ} (G : MatrixGraph (2*(d+1)))
    (hG : 2*(d+1) ≤ b+1) (k : ℕ) (coins : BitString) : Option (Fin (b+1)) :=
  GraphCountSample.sample (n:=2*d+1) G hG
    ((sampleInput (GraphInput.encode ⟨2*(d+1),G⟩) k).length+1) coins

noncomputable def sample {b : ℕ} (k m : ℕ) : State b → CoinTape m → Option (Fin (b+1))
  | ⟨0,_⟩,_ => none
  | ⟨d+1,none⟩,_ => none
  | ⟨d+1,some G⟩,r => activeSample G.val G.property k (List.ofFn r)

lemma active_child_count {b d : ℕ} (G : MatrixGraph (2*(d+1)))
    (hG : 2*(d+1) ≤ b+1) (j : Fin (b+1)) :
    GraphCountSample.childCount (n:=2*d+1) G j=count (child ⟨d+1,some ⟨G,hG⟩⟩ j) := by
  rw [child_count]
  rfl

 theorem activeSample_bytes {b d : ℕ} (G : MatrixGraph (2*(d+1)))
    (hG : 2*(d+1) ≤ b+1) (k : ℕ) (coins : BitString) :
    firstPartnerValue (GraphFunctional.evaluate
      (pairBits (sampleInput (GraphInput.encode ⟨2*(d+1),G⟩) k) coins))=
      encodePartner (activeSample G hG k coins) := by
  rw [GraphFunctional.evaluate_canonical]
  exact GraphCountSample.sample_bytes G hG _ coins

 theorem sample_active_bytes {b d : ℕ} (G : MatrixGraph (2*(d+1)))
    (hG : 2*(d+1) ≤ b+1) (k m : ℕ) (r : CoinTape m) :
    firstPartnerValue (GraphFunctional.evaluate
      (pairBits (sampleInput (stateBytes (b:=b) ⟨d+1,some ⟨G,hG⟩⟩) k) (List.ofFn r)))=
      encodePartner (sample k m ⟨d+1,some ⟨G,hG⟩⟩ r) :=
  activeSample_bytes G hG k (List.ofFn r)

 theorem activeSample_sound {b d : ℕ} (G : MatrixGraph (2*(d+1)))
    (hG : 2*(d+1) ≤ b+1) (k : ℕ) (coins : BitString) (j : Fin (b+1))
    (hj : activeSample G hG k coins=some j) : 0 < count (child ⟨d+1,some ⟨G,hG⟩⟩ j) := by
  rw [← active_child_count G hG j]
  exact GraphCountSample.sample_sound G hG _ coins j hj

 theorem sample_sound {b : ℕ} (k m : ℕ) (s : State b) (r : CoinTape m) (j : Fin (b+1))
    (h : sample k m s r=some j) : 0 < count (child s j) := by
  rcases s with ⟨d,G⟩
  cases d with
  | zero => simp [sample] at h
  | succ d =>
    cases G with
    | none => simp [sample] at h
    | some G => exact activeSample_sound G.val G.property k (List.ofFn r) j h

lemma input_precision_bounds {n : ℕ} (G : MatrixGraph n) (k : ℕ) :
    n ≤ (sampleInput (GraphInput.encode ⟨n,G⟩) k).length+1 ∧
      k+1 ≤ (sampleInput (GraphInput.encode ⟨n,G⟩) k).length+1 := by
  have hn := GraphInput.decode_vertices_bound (GraphInput.decode_encode ⟨n,G⟩)
  change n ≤ (GraphInput.encode ⟨n,G⟩).length at hn
  rw [sampleInput_length]
  constructor <;> omega

 theorem activeSample_bias {b d : ℕ} (G : MatrixGraph (2*(d+1)))
    (hG : 2*(d+1) ≤ b+1) (hclass : Quasimonotone G.graph) (k m : ℕ)
    (hm : sampleBits b k ≤ m) (hc : 0 < perfectMatchingCount G.graph) (j : Fin (b+1)) :
    |coinProbability m (fun r => activeSample G hG k (List.ofFn r)=some j)-
      (reduction b).branchProbability ⟨d+1,some ⟨G,hG⟩⟩ j| ≤ 1/(2^k : ℚ) := by
  have h := GraphCountSample.bias G hG hclass
    ((sampleInput (GraphInput.encode ⟨2*(d+1),G⟩) k).length+1) k m
    (input_precision_bounds G k).1 (input_precision_bounds G k).2
    ((sampleBits_bound G hG k).trans hm) hc j
  rw [active_child_count G hG j] at h
  exact h

/-- Bias is needed only on the hereditary graph promise, never on arbitrary
malformed or off-promise inputs. Exact support soundness above is unconditional. -/
theorem sample_bias {b : ℕ} (k m : ℕ) (hm : sampleBits b k ≤ m)
    (s : State b) (hs : promised s) (hc : 0 < count s) (hr : 0 < rank s) (j : Fin (b+1)) :
    |coinProbability m (fun r => sample k m s r=some j)-
      (reduction b).branchProbability s j| ≤ 1/(2^k : ℚ) := by
  rcases s with ⟨d,G⟩
  cases d with
  | zero => exact False.elim (Nat.lt_irrefl 0 hr)
  | succ d =>
    cases G with
    | none => exact False.elim (Nat.lt_irrefl 0 hc)
    | some G => exact activeSample_bias G.val G.property hs k m hm hc j

/-- No matching-existence decision is queried in zero handling. A zero-count
state cannot contain the full matching witnessed by any successful sample. -/
theorem sample_zero {b : ℕ} (k m : ℕ) (s : State b) (hc : count s=0) :
    ∀ r, sample k m s r=none := by
  classical
  rcases s with ⟨d,G⟩
  cases d with
  | zero => simp [sample]
  | succ d =>
    cases G with
    | none => simp [sample]
    | some G =>
      intro r
      simp only [sample]
      unfold activeSample GraphCountSample.sample
      cases hx : GraphCountSample.sampled G.val
          ((sampleInput (GraphInput.encode ⟨2*(d+1),G.val⟩) k).length+1) (List.ofFn r) with
      | none => simp [hx]
      | some P =>
        have hp : 0 < perfectMatchingCount G.val.graph := by
          rw [perfectMatchingCount_eq_partners]
          exact Fintype.card_pos_iff.mpr ⟨P⟩
        change perfectMatchingCount G.val.graph=0 at hc
        omega

end HiddenCircuits.Approximation.SelfReduction.GraphCount
