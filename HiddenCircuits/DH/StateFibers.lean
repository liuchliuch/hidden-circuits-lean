import HiddenCircuits.DH.JoinFactors

/-! Regroup actual finite graph matchings and partial bijections by their numeric state. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable {V W : Type*} {G : SimpleGraph V} {T : Set V}

noncomputable def activeMatchingEquivStates [Fintype V] : ActiveMatching G T ≃
    (Σ i : Fin (Fintype.card V + 1), BagState G T i.val) where
  toFun p := ⟨⟨uncovered p.val,Nat.lt_succ_of_le (uncovered_le_card p.val)⟩,
    ⟨p.val,p.property,rfl⟩⟩
  invFun x := ⟨x.2.val,x.2.property.1⟩
  left_inv p := rfl
  right_inv x := by
    rcases x with ⟨⟨i,hi⟩,p,hp,hpi⟩
    dsimp only at hpi
    subst i
    rfl

/-- Grouping by the uncovered count multiplies each value by the actual state cardinality. -/
lemma sum_activeMatching [Fintype V] (f : ℕ → ℕ) :
    (∑ p : ActiveMatching G T, f (uncovered p.val)) =
      ∑ i : Fin (Fintype.card V + 1), Fintype.card (BagState G T i.val) * f i.val := by
  classical
  rw [Fintype.sum_equiv activeMatchingEquivStates (fun p => f (uncovered p.val))
    (fun x => f x.1.val) (fun _ => rfl)]
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,smul_eq_mul]

namespace PartialPairs
variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

lemma rank_le_card (c : PartialPairs V W) : c.rank ≤ Fintype.card V := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

lemma rank_le_card_right (c : PartialPairs V W) : c.rank ≤ Fintype.card W := by
  rw [rank,c.domain_card_eq]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

/-- Finite rank partition with an independently proved upper bound. -/
noncomputable def rankFilterEquiv (n : ℕ) (hn : ∀ c : PartialPairs V W, c.rank ≤ n)
    (P : ℕ → Prop) :
    {c : PartialPairs V W // P c.rank} ≃
      (Σ r : Fin (n+1), {c : PartialPairs V W // c.rank = r.val ∧ P r.val}) where
  toFun c := ⟨⟨c.val.rank,Nat.lt_succ_of_le (hn c.val)⟩,c.val,rfl,c.property⟩
  invFun x := ⟨x.2.val, x.2.property.1.symm ▸ x.2.property.2⟩
  left_inv c := rfl
  right_inv x := by
    rcases x with ⟨⟨r,hr⟩,c,he,hp⟩
    dsimp only at he
    subst r
    rfl

lemma rankFiber_card (r : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Fintype.card {c : PartialPairs V W // c.rank = r ∧ P r} =
      if P r then (Fintype.card V).choose r * (Fintype.card W).choose r * r.factorial else 0 := by
  classical
  by_cases hp : P r
  · rw [if_pos hp]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight
      (fun c : PartialPairs V W => show (c.rank = r ∧ P r) ↔ c.rank = r by simp only [hp,and_true]))]
    exact rank_card r
  · rw [if_neg hp]
    haveI : IsEmpty {c : PartialPairs V W // c.rank = r ∧ P r} := ⟨fun c => hp c.property.2⟩
    exact Fintype.card_eq_zero

/-- Cardinality of any rank predicate is the sum of the genuine cross-pair fibers. -/
lemma rankFilter_card (n : ℕ) (hn : ∀ c : PartialPairs V W, c.rank ≤ n)
    (P : ℕ → Prop) [DecidablePred P] :
    Fintype.card {c : PartialPairs V W // P c.rank} =
      ∑ r : Fin (n+1), if P r.val then
        (Fintype.card V).choose r.val * (Fintype.card W).choose r.val * r.val.factorial else 0 := by
  classical
  rw [Fintype.card_congr (rankFilterEquiv n hn P)]
  simp only [Fintype.card_sigma,rankFiber_card]

end PartialPairs
end HiddenCircuits.DH
