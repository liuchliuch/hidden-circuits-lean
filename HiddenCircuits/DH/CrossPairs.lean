import HiddenCircuits.GraphCounting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Finset.Powerset

/-! Exact choices of endpoints and bijections for cross-bag matching edges. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable (V W : Type*) [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

abbrev Selected (r : ℕ) := ↥((Finset.univ : Finset V).powersetCard r)

lemma selected_card (r : ℕ) : Fintype.card (Selected V r) = (Fintype.card V).choose r := by
  simp [Selected]

lemma selected_size {r : ℕ} (s : Selected V r) : s.val.card = r :=
  (Finset.mem_powersetCard.mp s.property).2

/-- A cross matching is two equally sized endpoint sets and a bijection between them. -/
abbrev CrossPairs (r : ℕ) := Σ s : Selected V r, Σ t : Selected W r, (s.val ≃ t.val)

/-- The true-twin multiplicity, counted as concrete endpoint-and-bijection choices. -/
theorem crossPairs_card (r : ℕ) :
    Fintype.card (CrossPairs V W r) =
      (Fintype.card V).choose r * (Fintype.card W).choose r * r.factorial := by
  classical
  have he (s : Selected V r) (t : Selected W r) :
      Fintype.card (s.val ≃ t.val) = r.factorial := by
    let e := Finset.equivOfCardEq ((selected_size V s).trans (selected_size W t).symm)
    rw [Fintype.card_equiv e,Fintype.card_coe,selected_size]
  simp only [CrossPairs,Fintype.card_sigma]
  simp_rw [he]
  simp [mul_assoc]

/-- Covering every absorbed-side vertex is an injection into the surviving uncovered set. -/
theorem pendantAssignments_card :
    Fintype.card (W ↪ V) = (Fintype.card V).descFactorial (Fintype.card W) :=
  Fintype.card_embedding_eq

/-- The equivalent binomial-times-factorial form used by the bag update. -/
theorem pendantAssignments_card_choose :
    Fintype.card (W ↪ V) =
      (Fintype.card V).choose (Fintype.card W) * (Fintype.card W).factorial := by
  rw [Fintype.card_embedding_eq,Nat.descFactorial_eq_factorial_mul_choose]
  ring

end HiddenCircuits.DH
