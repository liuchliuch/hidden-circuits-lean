import HiddenCircuits.Complexity.FPSharpP
import HiddenCircuits.Complexity.OracleElimination.Polynomial

/-! Literal natural-valued FP = #P consequences. The forward containment is
proved by a compute-and-compare verifier; the reverse containment uses the
proved unrestricted finite-TM2 elimination of a polynomial-time oracle. -/
namespace HiddenCircuits.Complexity

/-- Literal class equality is equivalent to the nontrivial containment. -/
theorem fp_eq_sharpP_iff : FP_eq_SharpP ↔ ∀ f : BitString → ℕ,SharpP f → FP f := by
  constructor
  · intro h f;exact (h f).mpr
  · intro h f;exact ⟨FP.sharpP,h f⟩

/-- An arbitrary polynomial-time algorithm for a #P-hard target collapses the
full original finite-TM2 classes. No restricted solver model is introduced. -/
theorem SharpPHard.fp_eq_sharpP {g : BitString → ℕ} (h : SharpPHard g) (hg : FP g) :
    FP_eq_SharpP :=
  fp_eq_sharpP_iff.mpr (h.sharpP_subset_fp hg)

/-- Standard conditional impossibility: FP ≠ #P rules out an FP algorithm for
every #P-hard oracle. -/
theorem SharpPHard.not_fp {g : BitString → ℕ} (h : SharpPHard g)
    (hsep : ¬FP_eq_SharpP) : ¬FP g :=
  fun hg => hsep (h.fp_eq_sharpP hg)

/-- For a complete total counting problem, FP membership exactly characterizes
the class collapse. -/
theorem SharpPComplete.fp_iff_collapse {g : BitString → ℕ} (h : SharpPComplete g) :
    FP g ↔ FP_eq_SharpP :=
  ⟨h.2.fp_eq_sharpP,fun he => (he g).mpr h.1⟩

end HiddenCircuits.Complexity
