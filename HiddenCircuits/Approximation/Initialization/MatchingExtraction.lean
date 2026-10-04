import HiddenCircuits.Approximation.Initialization.ResidualTest

/-! A finite adaptive sequence of actual residual Tutte tests.
The success marker records the search's termination event; the companion
ForwardExtraction accumulator constructs the returned matching itself. -/
namespace HiddenCircuits.Approximation.Initialization.MatchingExtraction
open SelfReduction ResidualTest
open scoped BigOperators

variable {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]

def select (k : ℕ) (s : MatchingState b) (r : CoinTape (bits b k)) : Option (Fin (b+1)) :=
  (List.finRange (b+1)).find? (fun v => statePositive G k (matchingChild G s v) r)

theorem select_sound (k : ℕ) (s : MatchingState b) (r : CoinTape (bits b k))
    {v : Fin (b+1)} (h : select G k s r = some v) :
    0 < matchingStateCount G (matchingChild G s v) :=
  statePositive_sound G k _ r (List.find?_some
    (p := fun w => statePositive G k (matchingChild G s w) r) (a := v) h)

theorem select_failure (k : ℕ) (s : MatchingState b)
    (hs : 0 < matchingStateCount G s) (hr : 0 < matchingRank s) :
    coinProbability (bits b k) (fun r => select G k s r = none) ≤ 1/(2^k : ℚ) := by
  have he : ∃ v, 0 < matchingStateCount G (matchingChild G s v) := by
    by_contra! h
    have hz : ∀ v, matchingStateCount G (matchingChild G s v) = 0 :=
      fun v => Nat.eq_zero_of_le_zero (h v)
    rw [matchingState_recurrence G s hr] at hs
    simp [hz] at hs
  obtain ⟨v, hv⟩ := he
  apply (coinProbability_mono (E := fun r => select G k s r = none)
    (F := fun r => statePositive G k (matchingChild G s v) r = false) ?_).trans
    (statePositive_failure G k _ hv)
  intro r h
  exact Bool.eq_false_iff.mpr ((List.find?_eq_none.mp h) v (List.mem_finRange v))

def leaf (s : MatchingState b) : Option Unit :=
  match s with
  | ⟨0, some _⟩ => some ()
  | _ => none

def run (k : ℕ) : (d : ℕ) → MatchingState b →
    (Fin d → CoinTape (bits b k)) → Option Unit
  | 0, s, _ => leaf s
  | d+1, s, r =>
      match select G k s (r 0) with
      | none => none
      | some v => (run k d (matchingChild G s v) (fun i => r i.succ)).map id

theorem run_failure (k d : ℕ) (s : MatchingState b)
    (hs : 0 < matchingStateCount G s) (hr : matchingRank s = d) :
    probability (fun r => run G k d s r = none) ≤ (d : ℚ)/(2^k : ℚ) := by
  classical
  induction d generalizing s with
  | zero =>
    rcases s with ⟨e,U⟩
    change e = 0 at hr
    subst e
    cases U with
    | none => exact False.elim (Nat.lt_irrefl 0 hs)
    | some U => simp [run,leaf]
  | succ d ih =>
    rw [probability_fin_succ]
    have hb (a : CoinTape (bits b k)) :
        probability (fun r : Fin d → CoinTape (bits b k) =>
          run G k (d+1) s (Fin.cons a r) = none) ≤
          (if select G k s a = none then 1 else 0) + (d : ℚ)/(2^k : ℚ) := by
      cases ha : select G k s a with
      | none =>
        simp only [run,Fin.cons_zero,ha,probability_true,if_true]
        exact le_add_of_nonneg_right (by positivity)
      | some v =>
        have hc := select_sound G k s a ha
        have hdr : matchingRank (matchingChild G s v) = d := by
          have hh := matchingChild_rank G s v (by omega)
          omega
        simpa [run,ha] using ih (matchingChild G s v) hc hdr
    apply (mean_mono hb).trans
    rw [mean_add,mean_const,mean_indicator,probability_coinTape]
    have hf := select_failure G k s hs (by omega)
    push_cast
    rw [add_div]
    linarith

def runCoins (k d : ℕ) (s : MatchingState b) (r : CoinTape (d*bits b k)) : Option Unit :=
  run G k d s (splitBlocks d (bits b k) r)

theorem runCoins_failure (k d : ℕ) (s : MatchingState b)
    (hs : 0 < matchingStateCount G s) (hr : matchingRank s = d) :
    coinProbability (d*bits b k) (fun r => runCoins G k d s r = none) ≤ (d : ℚ)/(2^k : ℚ) := by
  rw [←probability_coinTape]
  unfold runCoins
  rw [probability_equiv (splitBlocks d (bits b k)) (fun r => run G k d s r = none)]
  exact run_failure G k d s hs hr

end HiddenCircuits.Approximation.Initialization.MatchingExtraction
