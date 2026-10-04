import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Finite order ranks preserve ties. These are comparison counts, not chosen
permutations, so repeated represented coordinates keep their labeled vertices. -/
namespace HiddenCircuits.GraphReduction.FiniteOrderRank
variable {α : Type*} [LinearOrder α]

def rank (s : Finset α) (a : α) : ℕ := (s.filter (· < a)).card

lemma mono (s : Finset α) {a b : α} (h : a ≤ b) : rank s a ≤ rank s b := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans_le h⟩

lemma strict {s : Finset α} {a b : α} (ha : a ∈ s) (h : a < b) :
    rank s a < rank s b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1,hx.2.trans h⟩
  · intro he
    have hx : a ∈ s.filter (· < b) := by simp [ha,h]
    rw [←he] at hx
    simpa using hx

lemma le_iff {s : Finset α} {a b : α} (hb : b ∈ s) :
    rank s a ≤ rank s b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    exact (Nat.not_lt_of_ge h) (strict hb (lt_of_not_ge hn))
  · exact mono s

lemma lt_card {s : Finset α} {a : α} (ha : a ∈ s) : rank s a < s.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have hx : a ∈ s.filter (· < a) := by rw [he]; exact ha
  simpa using hx

lemma int_succ {s : Finset ℤ} {a : ℤ} (ha : a ∈ s) : rank s (a+1) = rank s a+1 := by
  have h : s.filter (· < a+1) = insert a (s.filter (· < a)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_insert]
    constructor
    · rintro ⟨hx,hxa⟩
      by_cases he : x=a
      · exact Or.inl he
      · exact Or.inr ⟨hx,by omega⟩
    · rintro (rfl|⟨hx,hxa⟩)
      · exact ⟨ha,by omega⟩
      · exact ⟨hx,by omega⟩
  unfold rank
  rw [h,Finset.card_insert_of_notMem]
  simp

lemma int_two_le {s : Finset ℤ} {a : ℤ} (ha : a ∈ s) (ha' : a+1 ∈ s) :
    rank s a+2 ≤ s.card := by
  have h := lt_card ha'
  rw [int_succ ha] at h
  omega

end HiddenCircuits.GraphReduction.FiniteOrderRank
