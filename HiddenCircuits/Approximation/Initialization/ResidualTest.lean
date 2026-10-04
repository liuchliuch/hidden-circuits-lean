import HiddenCircuits.Approximation.Initialization.TutteCoins
import HiddenCircuits.Approximation.SelfReduction.MatchingDeletion
import HiddenCircuits.Approximation.SamplerRuntime.CoinLists
import Mathlib.Data.Finset.Sort

/-! Exact bounded fair-coin tests of the actual induced residual graph.
Vertices keep their inherited increasing order. Unused random suffixes are
discarded by a proved finite-uniform prefix projection. -/
namespace HiddenCircuits.Approximation.Initialization.ResidualTest
open SelfReduction

abbrev takeTape {a M : ℕ} (h : a ≤ M) (r : CoinTape M) : CoinTape a :=
  SamplerRuntime.CoinLists.restrictTape h r

theorem probability_prefix {a M : ℕ} (h : a ≤ M) (E : CoinTape a → Prop) :
    coinProbability M (fun r => E (takeTape h r)) = coinProbability a E :=
  SamplerRuntime.CoinLists.probability_restrict h E

def bits (b k : ℕ) : ℕ := (b+1)*(b+1)*(b+1+k)

def vertex {n : ℕ} (U : Finset (Fin n)) (i : Fin U.card) : Fin n :=
  (U.orderIsoOfFin rfl i).val

def graph {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) : SimpleGraph (Fin U.card) :=
  G.comap (vertex U)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) :
    DecidableRel (graph G U).Adj := fun _ _ => inferInstanceAs (Decidable (G.Adj _ _))

def graphIso {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    graph G U ≃g G.induce (U : Set (Fin n)) where
  toEquiv := (U.orderIsoOfFin rfl).toEquiv
  map_rel_iff' := by intro i j; rfl

theorem budget {b : ℕ} (U : Finset (Fin (b+1))) (k : ℕ) :
    U.card*U.card*(b+1+k) ≤ bits b k := by
  have h : U.card ≤ b+1 := by simpa using U.card_le_univ
  unfold bits
  gcongr

def positive {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (U : Finset (Fin (b+1))) (k : ℕ) (r : CoinTape (bits b k)) : Bool :=
  decide ((TuttePolynomial.matrix (graph G U)
    (TutteCoins.draw (U.card*U.card) (b+1+k) (takeTape (budget U k) r))).det ≠ 0)

def statePositive {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (k : ℕ) (s : MatchingState b) (r : CoinTape (bits b k)) : Bool :=
  match s.2 with
  | none => false
  | some U => positive G U.val k r

theorem positive_sound {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (U : Finset (Fin (b+1))) (k : ℕ) (r : CoinTape (bits b k))
    (h : positive G U k r = true) :
    Nonempty (PerfectMatching (G.induce (U : Set (Fin (b+1))))) := by
  have hh := TuttePolynomial.matrix_sound (graph G U) _ (of_decide_eq_true h)
  exact hh.map (perfectMatchingIsoEquiv (graphIso G U))

theorem statePositive_sound {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (k : ℕ) (s : MatchingState b) (r : CoinTape (bits b k))
    (h : statePositive G k s r = true) : 0 < matchingStateCount G s := by
  rcases s with ⟨d, U⟩
  cases U with
  | none => simp [statePositive] at h
  | some U =>
    exact Fintype.card_pos_iff.mpr (positive_sound G U.val k r h)

theorem positive_failure {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (U : Finset (Fin (b+1))) (k : ℕ)
    (h : 0 < perfectMatchingCount (G.induce (U : Set (Fin (b+1)))) ) :
    coinProbability (bits b k) (fun r => positive G U k r = false) ≤ 1/(2^k : ℚ) := by
  have hG : Nonempty (PerfectMatching (graph G U)) := by
    apply Fintype.card_pos_iff.mp
    rw [←perfectMatchingCount_congr (graphIso G U)] at h
    exact h
  have hh := TutteCoins.graph_false_zero_bound (graph G U) hG (b+1+k)
  have he : coinProbability (bits b k) (fun r => positive G U k r = false) =
      coinProbability (U.card*U.card*(b+1+k))
        (fun r => (TuttePolynomial.matrix (graph G U)
          (TutteCoins.draw (U.card*U.card) (b+1+k) r)).det = 0) := by
    simp only [positive, decide_eq_false_iff_not, not_not]
    exact probability_prefix (budget U k) (fun r =>
      (TuttePolynomial.matrix (graph G U)
        (TutteCoins.draw (U.card*U.card) (b+1+k) r)).det = 0)
  rw [he]
  refine hh.trans ?_
  have hcard : U.card ≤ b+1 := by simpa using U.card_le_univ
  have hpow : (U.card : ℚ) ≤ (2:ℚ)^(b+1) := by
    exact_mod_cast hcard.trans (b+1).lt_two_pow_self.le
  rw [pow_add]
  calc
    (U.card : ℚ)/(2^(b+1)*2^k) ≤ 2^(b+1)/(2^(b+1)*2^k) := by gcongr
    _ = 1/(2^k : ℚ) := by field_simp

theorem statePositive_failure {b : ℕ} (G : SimpleGraph (Fin (b+1))) [DecidableRel G.Adj]
    (k : ℕ) (s : MatchingState b) (h : 0 < matchingStateCount G s) :
    coinProbability (bits b k) (fun r => statePositive G k s r = false) ≤ 1/(2^k : ℚ) := by
  rcases s with ⟨d, U⟩
  cases U with
  | none => exact False.elim (Nat.lt_irrefl 0 h)
  | some U => exact positive_failure G U.val k h

end HiddenCircuits.Approximation.Initialization.ResidualTest
