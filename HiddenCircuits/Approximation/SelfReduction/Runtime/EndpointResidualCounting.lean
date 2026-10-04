import HiddenCircuits.Approximation.SelfReduction.Runtime.EndpointResidualBudget
import HiddenCircuits.Approximation.SelfReduction.ObservedSoundness

/-! Natural-only, early-zero counting specification for canonical endpoints.
The supplied sampler is the actual initialized endpoint experiment. This file
connects every tape, including statistically bad tapes, to the proved estimator. -/
namespace HiddenCircuits.Approximation.SelfReduction.EndpointResidual
open Complexity

/-- Empirical selected factors along literal canonical endpoint deletions. -/
def naturalCounts {b : ℕ} (precision m T h : ℕ) :
    (d : ℕ) → State b → (Fin d → StageTape (CoinTape m) T h) → List ℕ
  | 0,_,_ => []
  | d+1,s,tapes =>
      let j := naturalSelectedBranch b T h (sample precision m) s (tapes 0)
      naturalAmplifiedCount (fun a => sample precision m s a=some j) T h (tapes 0)::
        naturalCounts precision m T h d (child s j) (fun i => tapes i.succ)

/-- Stop before issuing any further sampler call or constructing a child when
the selected empirical factor is zero. -/
def shortCounts {b : ℕ} (precision m T h : ℕ) :
    (d : ℕ) → State b → (Fin d → StageTape (CoinTape m) T h) → Option (List ℕ)
  | 0,_,_ => some []
  | d+1,s,tapes =>
      let j := naturalSelectedBranch b T h (sample precision m) s (tapes 0)
      let c := naturalAmplifiedCount (fun a => sample precision m s a=some j) T h (tapes 0)
      if c=0 then none else
        (shortCounts precision m T h d (child s j) (fun i => tapes i.succ)).map (c::·)

lemma naturalCounts_eq {b : ℕ} (precision m T h d : ℕ) (hT : 0<T) (s : State b)
    (tapes : Fin d → StageTape (CoinTape m) T h) :
    naturalCounts precision m T h d s tapes=
      selectedCounts (reduction b) (sample precision m) T h d s tapes := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    simp only [naturalCounts,selectedCounts,naturalSelectedBranch_eq b T h hT,
      naturalAmplifiedCount_eq _ _ _ hT,ih,selectedCount,countingStep,reduction]

lemma shortCounts_some {b : ℕ} (precision m T h d : ℕ) (s : State b)
    (tapes : Fin d → StageTape (CoinTape m) T h) (xs : List ℕ)
    (hx : shortCounts precision m T h d s tapes=some xs) :
    naturalCounts precision m T h d s tapes=xs := by
  induction d generalizing s xs with
  | zero => simpa [shortCounts,naturalCounts] using hx
  | succ d ih =>
    simp only [shortCounts] at hx
    split_ifs at hx with hz
    obtain ⟨ys,hy,hcons⟩ := Option.map_eq_some_iff.mp hx
    subst xs
    simp only [naturalCounts]
    congr 1
    exact ih _ _ _ hy

lemma shortCounts_none {b : ℕ} (precision m T h d : ℕ) (s : State b)
    (tapes : Fin d → StageTape (CoinTape m) T h)
    (hx : shortCounts precision m T h d s tapes=none) :
    (naturalCounts precision m T h d s tapes).prod=0 := by
  induction d generalizing s with
  | zero => simp [shortCounts] at hx
  | succ d ih =>
    simp only [shortCounts] at hx
    split_ifs at hx with hz
    · simp only [naturalCounts,List.prod_cons,hz,zero_mul]
    · have ht := Option.map_eq_none_iff.mp hx
      simp only [naturalCounts,List.prod_cons]
      rw [ih _ _ ht,mul_zero]

theorem chosenCount_child_positive {b : ℕ} (precision m T h : ℕ) (s : State b)
    (tape : StageTape (CoinTape m) T h)
    (hp : 0<naturalAmplifiedCount (fun a => sample precision m s a=
      some (naturalSelectedBranch b T h (sample precision m) s tape)) T h tape) :
    0<count (child s (naturalSelectedBranch b T h (sample precision m) s tape)) := by
  obtain ⟨a,ha⟩ := naturalAmplifiedCount_positive _ T h tape hp
  exact sample_sound precision m s a _ ha

/-- A zero-count input cannot produce a successful sampled partner on any tape. -/
lemma sample_zero {b : ℕ} (precision m : ℕ) (s : State b) (hc : count s=0) :
    ∀r,sample precision m s r=none := by
  rcases s with ⟨d,E⟩
  cases d with
  | zero => simp [sample]
  | succ d =>
    cases E with
    | none => simp [sample]
    | some E =>
      have hn : E.val.startingPermutation=none := E.val.startingPermutation_none_iff.mpr (by
        intro he
        have hp := Fintype.card_pos_iff.mpr he
        change Fintype.card E.val.Permutations=0 at hc
        omega)
      simp [sample,activeSample,hn]

lemma naturalCounts_zero_product {b : ℕ} (precision m T h d : ℕ) (s : State b)
    (hc : count s=0) (tapes : Fin (d+1) → StageTape (CoinTape m) T h) :
    (naturalCounts precision m T h (d+1) s tapes).prod=0 := by
  have hs := sample_zero precision m s hc
  unfold naturalCounts
  dsimp only
  rw [naturalAmplifiedCount_false _ (fun a => by rw [hs];simp)]
  simp

def naturalOutput {b : ℕ} (precision m T h d : ℕ) (s : State b)
    (tapes : Fin d → StageTape (CoinTape m) T h) : BitString :=
  if s.2.isNone then encodeRatio 0 0 else
    reciprocalProductOutput (batchSize T) (naturalCounts precision m T h d s tapes)

def shortOutput {b : ℕ} (precision m T h d : ℕ) (s : State b)
    (tapes : Fin d → StageTape (CoinTape m) T h) : BitString :=
  if s.2.isNone then encodeRatio 0 0 else
    match shortCounts precision m T h d s tapes with
    | none => encodeRatio 0 0
    | some xs => reciprocalProductOutput (batchSize T) xs

/-- Early stopping preserves the exact output bytes on every random tape. -/
theorem shortOutput_eq {b : ℕ} (precision m T h d : ℕ) (s : State b)
    (tapes : Fin d → StageTape (CoinTape m) T h) :
    shortOutput precision m T h d s tapes=naturalOutput precision m T h d s tapes := by
  unfold shortOutput naturalOutput
  split_ifs with hrej
  · rfl
  · cases hx : shortCounts precision m T h d s tapes with
    | none =>
      have hp := shortCounts_none precision m T h d s tapes hx
      simp [reciprocalProductOutput,hp,encodeRatio]
    | some xs => rw [shortCounts_some precision m T h d s tapes xs hx]

/-- Exact zero needs no matching-existence oracle, only the distinct rejected
state marker and soundness of each actual sampled matching. -/
theorem shortOutput_zero {b : ℕ} (precision m T h d : ℕ) (s : State b)
    (hr : rank s=d) (hc : count s=0) (tapes : Fin d → StageTape (CoinTape m) T h) :
    decodeEstimate (shortOutput precision m T h d s tapes)=some 0 := by
  rw [shortOutput_eq]
  rcases s with ⟨sd,E⟩
  change sd=d at hr
  subst sd
  cases E with
  | none => simp [naturalOutput]
  | some E =>
    cases d with
    | zero =>
      have he := SamplerRuntime.EndpointFiber.count_empty E.val
      change Fintype.card E.val.Permutations=0 at hc
      omega
    | succ d =>
      have hz := naturalCounts_zero_product precision m T h d ⟨d+1,some E⟩ hc tapes
      simp [naturalOutput,reciprocalProductOutput,hz]

lemma shortOutput_decode_positive {b : ℕ} (precision m T h d : ℕ) (hT : 0<T) (s : State b)
    (hc : 0<count s) (tapes : Fin d → StageTape (CoinTape m) T h) :
    decodeEstimate (shortOutput precision m T h d s tapes)=
      some (countingEstimate (reduction b) (sample precision m) T h d s tapes) := by
  have hrej : s.2.isNone=false := by
    rcases s with ⟨d,E⟩
    cases E with
    | none => exact False.elim (Nat.lt_irrefl 0 hc)
    | some E => rfl
  rw [shortOutput_eq]
  simp only [naturalOutput,hrej,Bool.false_eq_true,if_false,naturalCounts_eq precision m T h d hT]
  exact countingOutput_decode (reduction b) (sample precision m) T h d s tapes
end HiddenCircuits.Approximation.SelfReduction.EndpointResidual
