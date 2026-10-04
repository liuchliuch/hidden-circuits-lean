import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountCounting
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountInvariant
import HiddenCircuits.Approximation.SelfReduction.UniformParameters

/-! Promised general-graph counting with oversized uniform physical loop budgets.
Any dominating global sample tape length is permitted. -/
namespace HiddenCircuits.Approximation.SelfReduction.GraphCount
open Complexity

/-- Exact zero and relative accuracy for oversized integer-only endpoint
counting, using the concrete endpoint sampler with any sufficient padded tape. -/
theorem shortOutput_oversized_guarantee {b : ℕ} (m T h d r k : ℕ)
    (hT : accuracyBudget b d r ≤ T) (hh : confidenceBudget b d k ≤ h)
    (hm : sampleBits b T ≤ m) (s : State b) (hs : promised s) (hrank : rank s=d) :
    (count s=0 → ∀tapes,decodeEstimate (shortOutput T m T h d s tapes)=some 0) ∧
    1-1/(2^k:ℚ) ≤ probability (fun tapes => ∃z,
      decodeEstimate (shortOutput T m T h d s tapes)=some z ∧ RelativeEstimate (count s) r z) := by
  classical
  have hT0 : 0<T := (accuracyBudget_pos b d r).trans_le hT
  constructor
  · exact fun hc tapes => shortOutput_zero T m T h d s hrank hc tapes
  · by_cases hc : count s=0
    · have hz := fun tapes => shortOutput_zero T m T h d s hrank hc tapes
      have he : probability (fun tapes => ∃z,
          decodeEstimate (shortOutput T m T h d s tapes)=some z ∧ RelativeEstimate (count s) r z)=1 := by
        have hevent : (fun tapes => ∃z,decodeEstimate (shortOutput T m T h d s tapes)=some z ∧
            RelativeEstimate (count s) r z)=(fun _ => True) := by
          funext tapes;apply propext;simp [hz,hc]
        rw [hevent,probability_true]
      rw [he]
      have hp : (0:ℚ) ≤ 1/2^k := by positivity
      linarith
    · have hc' : 0<count s := by omega
      have hbias : ∀state,promised state → 0<(reduction b).count state → 0<(reduction b).rank state → ∀j,
          |probability (fun a => sample T m state a=some j)-(reduction b).branchProbability state j| ≤ 1/(2^T:ℚ) := by
        intro state hstate hcount hr j
        rw [probability_coinTape]
        exact sample_bias T m hm state hstate hcount hr j
      have hf := CountReduction.oversized_failure_on_invariant (reduction b) promised
        (fun state hp j => child_promised state hp j) (sample T m) d r k T h hT hh hbias s hs hc' hrank
      have hevent : (fun tapes => ∃z,decodeEstimate (shortOutput T m T h d s tapes)=some z ∧
          RelativeEstimate (count s) r z) =
          (fun tapes => RelativeEstimate (count s) r (countingEstimate (reduction b) (sample T m) T h d s tapes)) := by
        funext tapes;apply propext
        simp only [shortOutput_decode_positive T m T h d hT0 s hc',Option.some.injEq,exists_eq_left']
      rw [hevent]
      rw [probability_compl] at hf
      change 1-probability (fun tapes => RelativeEstimate (count s) r
        (countingEstimate (reduction b) (sample T m) T h d s tapes)) ≤ 1/(2^k:ℚ) at hf
      linarith

/-- Uniform T=24(N+1)^3 and h=3N suffice for all original dimensions and
requested unary precision parameters bounded by N. -/
theorem shortOutput_uniform_guarantee {b : ℕ} (N m d r k : ℕ)
    (hb : b ≤ N) (hd : d ≤ N) (hr : r ≤ N) (hk : k ≤ N)
    (hm : sampleBits b (uniformAccuracy N) ≤ m) (s : State b) (hs : promised s) (hrank : rank s=d) :
    (count s=0 → ∀tapes,decodeEstimate
      (shortOutput (uniformAccuracy N) m (uniformAccuracy N) (uniformConfidence N) d s tapes)=some 0) ∧
    1-1/(2^k:ℚ) ≤ probability (fun tapes => ∃z,
      decodeEstimate (shortOutput (uniformAccuracy N) m (uniformAccuracy N) (uniformConfidence N) d s tapes)=some z ∧
      RelativeEstimate (count s) r z) :=
  shortOutput_oversized_guarantee m _ _ d r k (accuracyBudget_le_uniform b d r N hb hd hr)
    (confidenceBudget_le_uniform b d k N hb hd hk) hm s hs hrank

noncomputable def uniformOutput {b : ℕ} (N m d : ℕ) (s : State b)
    (tape : CoinTape (countingBits m (uniformAccuracy N) (uniformConfidence N) d)) : BitString :=
  shortOutput (uniformAccuracy N) m (uniformAccuracy N) (uniformConfidence N) d s
    (countingTapes m (uniformAccuracy N) (uniformConfidence N) d tape)

/-- The same guarantee for one physically partitioned fair-bit tape. -/
theorem uniformOutput_guarantee {b : ℕ} (N m d r k : ℕ)
    (hb : b ≤ N) (hd : d ≤ N) (hr : r ≤ N) (hk : k ≤ N)
    (hm : sampleBits b (uniformAccuracy N) ≤ m) (s : State b) (hs : promised s) (hrank : rank s=d) :
    (count s=0 → ∀tape,decodeEstimate (uniformOutput N m d s tape)=some 0) ∧
    1-1/(2^k:ℚ) ≤ coinProbability (countingBits m (uniformAccuracy N) (uniformConfidence N) d)
      (fun tape => ∃z,decodeEstimate (uniformOutput N m d s tape)=some z ∧ RelativeEstimate (count s) r z) := by
  obtain ⟨hz,hgood⟩ := shortOutput_uniform_guarantee N m d r k hb hd hr hk hm s hs hrank
  constructor
  · exact fun hc tape => hz hc _
  · rw [←probability_equiv (countingTapes m (uniformAccuracy N) (uniformConfidence N) d)
      (fun tapes => ∃z,decodeEstimate (shortOutput (uniformAccuracy N) m (uniformAccuracy N)
        (uniformConfidence N) d s tapes)=some z ∧ RelativeEstimate (count s) r z),probability_coinTape] at hgood
    exact hgood
end HiddenCircuits.Approximation.SelfReduction.GraphCount
