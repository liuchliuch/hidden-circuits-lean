import HiddenCircuits.GraphReduction.ProbePairCount

/-! The factorial-ratio form printed in the paper, including every small sample. -/
namespace HiddenCircuits.GraphReduction

/-- The standard two-injection extension formula agrees with the directly counted extensions.
If s<a, its falling-factorial factor is zero, so it makes no infeasible extensions. -/
theorem probePairBijection_card_square {X Y : Type*} [Fintype X] [Fintype Y]
    (h : Fintype.card X=Fintype.card Y) (s : ℕ) :
    Fintype.card (ProbePairBijection X Y (Fin s)) =
      (s.descFactorial (Fintype.card X))^2 * (s-Fintype.card X).factorial := by
  rw [probePairBijection_card h,Fintype.card_fin]
  by_cases hs : Fintype.card X≤s
  · rw [← Nat.factorial_mul_descFactorial hs]
    ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

/-- The exact rational normalization in equation (9.3), without an s≥a side condition. -/
theorem bipartiteProbe_factor (s a : ℕ) :
    (s.descFactorial a : ℚ)^2 * ((s-a).factorial : ℚ) / (s.factorial : ℚ) =
      (s.descFactorial a : ℚ) := by
  by_cases hs : a≤s
  · have he : ((s-a).factorial : ℚ) * (s.descFactorial a : ℚ) = (s.factorial : ℚ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial hs
    calc
      (s.descFactorial a : ℚ)^2 * ((s-a).factorial : ℚ) / (s.factorial : ℚ) =
          (s.descFactorial a : ℚ) * (((s-a).factorial : ℚ) * (s.descFactorial a : ℚ)) /
            (s.factorial : ℚ) := by ring
      _ = _ := by
        rw [he]
        exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero s)
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

end HiddenCircuits.GraphReduction
