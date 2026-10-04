import HiddenCircuits.GraphReduction.ProbePairBijection

/-! Kernel-checked counting of a complete probe pair, including insufficient probe sizes. -/
namespace HiddenCircuits.GraphReduction
variable {X Y P : Type*} [Fintype X] [Fintype Y] [Fintype P]

noncomputable instance (f : X ↪ P) : Fintype (ProbeRemainder (Y:=Y) f) := by
  classical
  unfold ProbeRemainder
  infer_instance

noncomputable instance : Fintype (ProbePairBijection X Y P) := by
  classical
  unfold ProbePairBijection
  infer_instance

 theorem probeRemainder_card (h : Fintype.card X=Fintype.card Y) (f : X ↪ P) :
    Fintype.card (ProbeRemainder (Y:=Y) f) = Fintype.card P := by
  have hc := Fintype.card_congr (probeTargetEquiv (Y:=Y) f)
  simp only [Fintype.card_sum] at hc
  omega

/-- The exact count is s! (s)_a without requiring a≤s. When a>s, the injection
factor itself is empty; there is no use of a negative factorial. -/
theorem probePairBijection_card (h : Fintype.card X=Fintype.card Y) :
    Fintype.card (ProbePairBijection X Y P) =
      (Fintype.card P).descFactorial (Fintype.card X) * (Fintype.card P).factorial := by
  classical
  rw [Fintype.card_congr (probePairBijectionEquiv (X:=X) (Y:=Y) (P:=P)),Fintype.card_sigma]
  have hc (f : X ↪ P) : Fintype.card (P ≃ ProbeRemainder (Y:=Y) f) =
      (Fintype.card P).factorial :=
    Fintype.card_equiv (Fintype.equivOfCardEq (probeRemainder_card h f).symm)
  simp_rw [hc]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_embedding_eq]

 theorem probePairBijection_balance (e : ProbePairBijection X Y P) :
    Fintype.card X=Fintype.card Y := by
  have hc := Fintype.card_congr e.val
  simp only [Fintype.card_sum] at hc
  omega

 theorem probePairBijection_card_unbalanced (h : Fintype.card X≠Fintype.card Y) :
    Fintype.card (ProbePairBijection X Y P) = 0 := by
  letI : IsEmpty (ProbePairBijection X Y P) := ⟨fun e => h (probePairBijection_balance e)⟩
  exact Fintype.card_eq_zero

/-- The normalized local probe count, as an exact rational number. -/
theorem normalized_probePair_count (h : Fintype.card X=Fintype.card Y) (s : ℕ) :
    (Fintype.card (ProbePairBijection X Y (Fin s)) : ℚ) / (s.factorial : ℚ) =
      (s.descFactorial (Fintype.card X) : ℚ) := by
  rw [probePairBijection_card h,Fintype.card_fin,Nat.cast_mul]
  exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero s)

 theorem probePair_count_insufficient (s : ℕ) (h : s < Fintype.card X) :
    Fintype.card (ProbePairBijection X Y (Fin s)) = 0 := by
  by_cases he : Fintype.card X=Fintype.card Y
  · rw [probePairBijection_card he,Fintype.card_fin,Nat.descFactorial_eq_zero_iff_lt.mpr h,zero_mul]
  · exact probePairBijection_card_unbalanced he

end HiddenCircuits.GraphReduction
