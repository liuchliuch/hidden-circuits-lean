import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
/-! Maximum selection and heavy-branch probability bounds. -/
namespace HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators
set_option maxHeartbeats 800000

def chooseMax {α : Type*} [LinearOrder α] : (n : ℕ) → (Fin (n+1) → α) → Fin (n+1)
  | 0, _ => 0
  | n+1, p =>
    let j := (chooseMax n (fun i => p i.succ)).succ
    if p 0 ≤ p j then j else 0

theorem chooseMax_spec {α : Type*} [LinearOrder α] (n : ℕ) (p : Fin (n+1) → α) :
    ∀ i, p i ≤ p (chooseMax n p) := by
  induction n with
  | zero =>
    intro i
    have hi : i=0 := by omega
    subst i
    exact le_rfl
  | succ n ih =>
    intro i
    have ht := ih (fun j => p j.succ)
    simp only [chooseMax]
    split_ifs with h
    · refine Fin.cases h (fun j => ht j) i
    · refine Fin.cases (le_refl _) (fun j => (ht j).trans (le_of_not_ge h)) i

theorem chooseMax_heavy (b : ℕ) (p q : Fin (b+1) → ℚ) (hsum : ∑ i, p i=1)
    (δ : ℚ) (hδ : δ ≤ 1/(4*(b+1 : ℚ))) (hgood : ∀ i, |q i-p i| ≤ δ) :
    1/(2*(b+1 : ℚ)) ≤ p (chooseMax b q) ∧
      1/(2*(b+1 : ℚ)) ≤ q (chooseMax b q) := by
  have hN : (0 : ℚ) < b+1 := by positivity
  have hb (i) : p i ≤ q (chooseMax b q)+δ := by
    have ha := (abs_le.mp (hgood i)).1
    have hm := chooseMax_spec b q i
    linarith
  have hs : 1 ≤ (b+1 : ℚ)*(q (chooseMax b q)+δ) := by
    calc
      1 = ∑ i, p i := hsum.symm
      _ ≤ ∑ _ : Fin (b+1), (q (chooseMax b q)+δ) := Finset.sum_le_sum (fun i _ => hb i)
      _ = _ := by simp; ring
  have hd := (le_div_iff₀ (by positivity : (0 : ℚ)<4*(b+1))).mp hδ
  have hp := (abs_le.mp (hgood (chooseMax b q))).2
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℚ)<2*(b+1))).2
    nlinarith
  · apply (div_le_iff₀ (by positivity : (0 : ℚ)<2*(b+1))).2
    nlinarith

theorem inverse_ratio_error (p q δ a : ℚ) (ha : 0<a) (hq : a≤q) (he : |q-p|≤δ) :
    |p/q-1|≤δ/a := by
  have hq0 : 0<q := ha.trans_le hq
  have hδ : 0≤δ := (abs_nonneg _).trans he
  have hh : p/q-1=(p-q)/q := by field_simp <;> ring
  rw [hh,abs_div,abs_of_pos hq0,abs_sub_comm p q]
  apply (div_le_div_iff₀ hq0 ha).2
  nlinarith
end HiddenCircuits.Approximation.SelfReduction
