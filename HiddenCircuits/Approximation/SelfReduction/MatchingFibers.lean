import HiddenCircuits.Approximation.SelfReduction.Branches
import HiddenCircuits.Approximation.MatchingSelfReduction

/-! Exact matching-specific fibers for the sampling-to-counting theorem. Invalid
partners have count zero; the empty graph has one (empty) perfect matching. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def allPartnerFiberEquiv {V : Type*} (G : SimpleGraph V) (u : V) :
    PerfectPartner G ≃ Σ v : V, EdgeFiber G u v where
  toFun p := ⟨p.val u, p, rfl⟩
  invFun q := q.2.val
  left_inv _ := rfl
  right_inv q := by
    rcases q with ⟨v,p,hp⟩
    dsimp
    cases hp
    rfl

/-- Number of completions after proposing a partner; rejected pairs have zero
completions, rather than accidentally counting an unconstrained residual graph. -/
noncomputable def matchingChildCount {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) : ℕ :=
  if G.Adj u v then perfectMatchingCount (G.induce (withoutPair u v)) else 0

theorem matchingChildCount_eq_fiber {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) :
    matchingChildCount G u v = Fintype.card (EdgeFiber G u v) := by
  classical
  by_cases h : G.Adj u v
  · rw [matchingChildCount, if_pos h, perfectMatchingCount_eq_partners]
    exact (Fintype.card_congr (edgeDeletionEquiv h)).symm
  · rw [matchingChildCount, if_neg h]
    symm
    apply (Fintype.card_eq_zero_iff).2
    refine ⟨fun p => h ?_⟩
    simpa [p.property] using p.val.property.2 u

/-- Summing over all named vertices includes all rejection branches correctly. -/
theorem matching_count_sum_all_partners {V : Type*} [Fintype V] (G : SimpleGraph V) (u : V) :
    perfectMatchingCount G = ∑ v, matchingChildCount G u v := by
  classical
  rw [perfectMatchingCount_eq_partners, Fintype.card_congr (allPartnerFiberEquiv G u), Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun v _ => (matchingChildCount_eq_fiber G u v).symm)

theorem matchingChildCount_pos {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V)
    (h : 0 < matchingChildCount G u v) :
    G.Adj u v ∧ 0 < perfectMatchingCount (G.induce (withoutPair u v)) := by
  unfold matchingChildCount at h
  split_ifs at h with ha
  · exact ⟨ha,h⟩
  · omega

theorem probability_eq_card {α : Type*} [Fintype α] (E : α → Prop) :
    probability E = (Fintype.card {a : α // E a} : ℚ)/Fintype.card α := by
  classical
  unfold probability mean
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- The uniform partner event is exactly the residual-count ratio used by the
self-reduction. This is a bijective theorem on actual perfect matchings. -/
theorem uniform_partner_probability {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V) :
    probability (fun p : PerfectPartner G => p.val u=v) =
      (matchingChildCount G u v : ℚ)/perfectMatchingCount G := by
  rw [probability_eq_card, perfectMatchingCount_eq_partners, matchingChildCount_eq_fiber]

/-- A sampler's failure marker remains visible; it cannot be conditioned away. -/
def sampledPartner {V : Type*} {G : SimpleGraph V} (u : V) (p : Option (PerfectPartner G)) : Option V :=
  p.map (fun q => q.val u)

/-- Any all-event near-uniform matching sampler supplies exactly the branch-bias
hypothesis needed by the checked counting scheme. -/
theorem sampledPartner_error {V : Type*} [Fintype V] (G : SimpleGraph V) (u v : V)
    (m : ℕ) (sample : CoinTape m → Option (PerfectPartner G)) (δ : ℚ)
    (h : ∀ E : Option (PerfectPartner G) → Prop,
      |coinProbability m (fun r => E (sample r)) - probability (fun p => E (some p))| ≤ δ) :
    |coinProbability m (fun r => sampledPartner u (sample r)=some v) -
      (matchingChildCount G u v : ℚ)/perfectMatchingCount G| ≤ δ := by
  have hh := h (fun p => sampledPartner u p=some v)
  simp only [sampledPartner, Option.map_some, Option.some.injEq] at hh
  rw [uniform_partner_probability] at hh
  exact hh

end HiddenCircuits.Approximation.SelfReduction
