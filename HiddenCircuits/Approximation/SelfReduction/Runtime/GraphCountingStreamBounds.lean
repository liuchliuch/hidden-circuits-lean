import HiddenCircuits.Approximation.SelfReduction.Runtime.CountDecision
import HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountCounting

/-! Every successful count stream has exactly one bounded positive factor per
actual deletion. These are the all-tape input invariants of the binary output
assembler, with no statistical-good-event premise. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
open Complexity
open HiddenCircuits.Approximation.SelfReduction.GraphCount

 theorem shortCounts_bounds {b : ℕ} (precision m T h d : ℕ) (s : SelfReduction.GraphCount.State b)
    (tapes : Fin d → StageTape (CoinTape m) T h) (xs : List ℕ)
    (hx : shortCounts precision m T h d s tapes=some xs) :
    xs.length=d ∧ ∀ c ∈ xs, 0 < c ∧ c ≤ batchSize T := by
  induction d generalizing s xs with
  | zero =>
    have he : xs=[] := by simpa only [shortCounts,Option.some.injEq] using hx.symm
    simp [he]
  | succ d ih =>
    simp only [shortCounts] at hx
    split_ifs at hx with hz
    obtain ⟨ys,hy,hcons⟩ := Option.map_eq_some_iff.mp hx
    subst xs
    have hh := ih _ _ _ hy
    constructor
    · simp only [List.length_cons,hh.1]
    · intro c hc
      rcases List.mem_cons.mp hc with hc | hc
      · subst c
        exact ⟨Nat.pos_of_ne_zero hz,naturalAmplifiedCount_le _ T h _⟩
      · exact hh.2 c hc

 theorem shortCounts_unary_length {b : ℕ} (precision m T h d : ℕ) (s : SelfReduction.GraphCount.State b)
    (tapes : Fin d → StageTape (CoinTape m) T h) (xs : List ℕ)
    (hx : shortCounts precision m T h d s tapes=some xs) :
    (unaryValues xs).length ≤ 2*d*(batchSize T+1) := by
  obtain ⟨hlen,hxs⟩ := shortCounts_bounds precision m T h d s tapes xs hx
  have hb := unaryValues_length_bound xs (batchSize T) (fun c hc => (hxs c hc).2)
  simpa only [hlen] using hb

end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCounting
