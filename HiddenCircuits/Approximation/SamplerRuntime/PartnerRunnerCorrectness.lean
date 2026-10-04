import HiddenCircuits.Approximation.SamplerRuntime.PartnerRunner
import HiddenCircuits.Approximation.SamplerRuntime.PartnerBudgetCorrectness

import HiddenCircuits.Approximation.UniformFinite
import HiddenCircuits.Approximation.SamplerRuntime.CoinLists

/-! Canonical-path correctness for the executed partner sampler. -/

/-! Canonical-path correctness for the executed partner sampler. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.PartnerRunner
open Complexity FiniteChains CoinLists GraphReduction
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma iterate_padded (G : MatrixGraph n) (N : ℕ) (hn : n≤N) (P : PerfectPartner G.graph)
    (r : CoinTape (PartnerBudget.bits N)) :
    PartnerIteration.iterate G (PartnerBudget.steps N) P (List.ofFn r)=
      runCoins (QuasimonotoneProof.PartnerSwitch.step G.graph (Nat.size n)) (PartnerBudget.steps N) P
        (restrictTape (PartnerBudget.tape_budget hn) r) := by
  let needed := PartnerIteration.width n*PartnerBudget.steps N
  have he : List.ofFn r=List.ofFn (restrictTape (PartnerBudget.tape_budget hn) r)++(List.ofFn r).drop needed := by
    rw [restrict_ofFn]
    exact (List.take_append_drop needed (List.ofFn r)).symm
  rw [he,PartnerIteration.iterate_append G _ P _ _ (by simp [PartnerIteration.width]),PartnerIteration.iterate_ofFn]

/-- All-events error for the actual runtime output, including the success marker. -/
theorem evaluate_event_error (G : MatrixGraph n) (hG : Quasimonotone G.graph) (N k : ℕ)
    (hn : n≤N) (hk : k≤N) (P : PerfectPartner G.graph) (A : Option BitString → Prop) :
    |coinProbability (PartnerBudget.bits N) (fun r => A (decodeSample (evaluate G N P (List.ofFn r))))-
      uniformProbability (PartnerOutput.witnesses G) A|≤1/(2^k:ℚ) := by
  simp only [evaluate,PartnerOutput.decode_success]
  simp_rw [iterate_padded G N hn P]
  rw [probability_restrict (PartnerBudget.tape_budget hn)
    (fun r => A (some (PartnerOutput.witness G (runCoins
      (QuasimonotoneProof.PartnerSwitch.step G.graph (Nat.size n)) (PartnerBudget.steps N) P r))))]
  rw [PartnerOutput.uniform_witnesses G P A]
  exact PartnerBudget.event_error G.graph hG P N k hn hk (fun x => A (some (PartnerOutput.witness G x)))

/-- The same literal sampler stage applies to supplied equal-length intervals;
no interval-order or cut certificate is needed by the switch machine. -/
theorem unitInterval_event_error (G : MatrixGraph n) (repr : UnitInterval.Representation G.graph)
    (N k : ℕ) (hn : n≤N) (hk : k≤N) (P : PerfectPartner G.graph) (A : Option BitString → Prop) :
    |coinProbability (PartnerBudget.bits N) (fun r => A (decodeSample (evaluate G N P (List.ofFn r))))-
      uniformProbability (PartnerOutput.witnesses G) A|≤1/(2^k:ℚ) :=
  evaluate_event_error G (HiddenCircuits.Approximation.UnitInterval.Representation.quasimonotone repr) N k hn hk P A

def afterInitialize (G : MatrixGraph n) (N : ℕ) (start : Option (PerfectPartner G.graph)) (tape : BitString) : BitString :=
  match start with | none => [] | some P => evaluate G N P tape

lemma initialized_sound (G : MatrixGraph n) (N : ℕ) (start : Option (PerfectPartner G.graph))
    (tape w : BitString) (h : decodeSample (afterInitialize G N start tape)=some w) : w∈PartnerOutput.witnesses G := by
  cases start with
  | none => simp [afterInitialize,decodeSample] at h
  | some P =>
    have he : PartnerOutput.witness G (PartnerIteration.iterate G (PartnerBudget.steps N) P tape)=w := by
      simpa only [afterInitialize,evaluate,PartnerOutput.decode_success,Option.some.injEq] using h
    rw [←he]
    exact PartnerOutput.witness_mem G _

lemma initialized_empty (G : MatrixGraph n) (N : ℕ) (start : Option (PerfectPartner G.graph)) (tape : BitString)
    (h : PartnerOutput.witnesses G=∅) : decodeSample (afterInitialize G N start tape)=none := by
  cases hd : decodeSample (afterInitialize G N start tape) with
  | none => rfl
  | some w => have hh := initialized_sound G N start tape w hd;simp [h] at hh

/-- Independent initialization and mixing errors add unconditionally. The
initializer hypothesis is exactly its separately proved false-empty bound. -/
theorem initialized_event_error (G : MatrixGraph n) (hG : Quasimonotone G.graph) (N k a : ℕ)
    (hn : n≤N) (hk : k+1≤N) (init : CoinTape a → Option (PerfectPartner G.graph))
    (hinit : Nonempty (PerfectPartner G.graph) → coinProbability a (fun r => init r=none)≤1/(2^N:ℚ))
    (A : Option BitString → Prop) :
    |coinProbability (a+PartnerBudget.bits N)
      (fun r => A (decodeSample (afterInitialize G N (init (splitTape a (PartnerBudget.bits N) r).1)
        (List.ofFn (splitTape a (PartnerBudget.bits N) r).2))))-
      uniformProbability (PartnerOutput.witnesses G) A|≤1/(2^k:ℚ) := by
  by_cases hnon : Nonempty (PerfectPartner G.graph)
  · obtain ⟨P⟩ := hnon
    have hu0 : 0≤uniformProbability (PartnerOutput.witnesses G) A := by
      rw [PartnerOutput.uniform_witnesses G P A]
      exact FiniteUniform.eventProbability_nonneg _
    have hu1 : uniformProbability (PartnerOutput.witnesses G) A≤1 := by
      rw [PartnerOutput.uniform_witnesses G P A]
      exact FiniteUniform.eventProbability_le_one _
    have hh := split_experiment_error
      (fun r t => A (decodeSample (afterInitialize G N (init r) (List.ofFn t))))
      (fun r => init r=none) (uniformProbability (PartnerOutput.witnesses G) A) (1/(2^N:ℚ)) (1/(2^N:ℚ))
      hu0 hu1 (by positivity)
      (by intro r hr;cases hi : init r with
          | none => exact (hr hi).elim
          | some Q => simpa only [hi,afterInitialize] using evaluate_event_error G hG N N hn le_rfl Q A)
      (hinit ⟨P⟩)
    refine hh.trans ?_
    have hpow : (1/(2^N:ℚ))≤1/(2^(k+1):ℚ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact pow_le_pow_right₀ (by norm_num) hk
    calc
      _ ≤ 1/(2^(k+1):ℚ)+1/(2^(k+1):ℚ) := add_le_add hpow hpow
      _ = _ := FiniteUniform.dyadic_split k
  · have he : PartnerOutput.witnesses G=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      exact fun hh => hnon ((PartnerOutput.witnesses_nonempty G).mp hh)
    have hout : ∀r,decodeSample (afterInitialize G N (init (splitTape a (PartnerBudget.bits N) r).1)
      (List.ofFn (splitTape a (PartnerBudget.bits N) r).2))=none := fun _ => initialized_empty G N _ _ he
    simp_rw [hout]
    simp [he,coinProbability_constant]

end HiddenCircuits.Approximation.SamplerRuntime.PartnerRunner
