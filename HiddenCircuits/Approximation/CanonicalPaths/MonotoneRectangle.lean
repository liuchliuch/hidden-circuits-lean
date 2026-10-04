import HiddenCircuits.Approximation.MonotoneStart

/-! The local matrix geometry that makes mountain-climber dislocations legal. -/
namespace HiddenCircuits.Approximation.CanonicalPaths

variable {n : ℕ}

def Allowed (E : MonotoneEndpoints n) (i j : Fin n) : Prop :=
  E.lo i ≤ j.val ∧ j.val < E.hi i

/-- Oppositely ordered edges in a monotone matrix complete their whole rectangle. -/
theorem rectangle_completion (E : MonotoneEndpoints n) {i k j l : Fin n}
    (hik : i ≤ k) (hjl : j ≤ l) (hil : Allowed E i l) (hkj : Allowed E k j) :
    Allowed E i j ∧ Allowed E k l := by
  have hlo := E.lo_mono hik
  have hhi := E.hi_mono hik
  change j.val ≤ l.val at hjl
  unfold Allowed at *
  omega

/-- Both off-cycle dislocations are legal when the two row intervals overlap.
The choice of upper/lower endpoint is driven by the order of the two columns. -/
theorem dislocation_edges (E : MonotoneEndpoints n) (a₀ a₁ b₀ b₁ x y : Fin n)
    (ha₀ : Allowed E a₀ x) (ha₁ : Allowed E a₁ x)
    (hb₀ : Allowed E b₀ y) (hb₁ : Allowed E b₁ y)
    (h₁ : min a₀ a₁ ≤ max b₀ b₁) (h₂ : min b₀ b₁ ≤ max a₀ a₁) :
    if x ≤ y then
      Allowed E (min b₀ b₁) x ∧ Allowed E (max a₀ a₁) y
    else
      Allowed E (max b₀ b₁) x ∧ Allowed E (min a₀ a₁) y := by
  have hamax : Allowed E (max a₀ a₁) x := by
    rcases le_total a₀ a₁ with h|h
    · simpa only [max_eq_right h] using ha₁
    · simpa only [max_eq_left h] using ha₀
  have hamin : Allowed E (min a₀ a₁) x := by
    rcases le_total a₀ a₁ with h|h
    · simpa only [min_eq_left h] using ha₀
    · simpa only [min_eq_right h] using ha₁
  have hbmax : Allowed E (max b₀ b₁) y := by
    rcases le_total b₀ b₁ with h|h
    · simpa only [max_eq_right h] using hb₁
    · simpa only [max_eq_left h] using hb₀
  have hbmin : Allowed E (min b₀ b₁) y := by
    rcases le_total b₀ b₁ with h|h
    · simpa only [min_eq_left h] using hb₀
    · simpa only [min_eq_right h] using hb₁
  split_ifs with hxy
  · exact rectangle_completion E h₂ hxy hbmin hamax
  · exact (rectangle_completion E h₁ (lt_of_not_ge hxy).le hamin hbmax).symm

end HiddenCircuits.Approximation.CanonicalPaths
