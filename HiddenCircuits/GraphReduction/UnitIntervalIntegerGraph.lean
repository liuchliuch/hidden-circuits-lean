import HiddenCircuits.GraphReduction.UnitIntervalQueryBounds

/-! The emitted integer equal-length diagrams are also literal strict-distance graphs. -/
namespace HiddenCircuits.GraphReduction
open UnitInterval

/-- The integer threshold is positive and is exactly the common closed-interval length plus one. -/
theorem unitQuery_threshold_positive (p h : ℕ) : 0<commonLength (2*p) h+1 := by
  have h := commonLength_positive (2*p) h
  omega

/-- The adjacency convention in Corollary10.4, for the actual submitted graph. -/
theorem unitIntervalQuery_integer_adj {p : ℕ} (w : List (CutPair p)) (S T : State (2*p) p)
    (s : ℕ) (u v : UnitOriginalVertex p w.length S T ⊕ (Fin (w.length+1) × Fin s)) :
    (unitIntervalQueryGraph (fun r => w.get r) S T s).Adj u v ↔
      u≠v ∧ |unitQueryLeftInteger w u-unitQueryLeftInteger w v|<commonLength (2*p) w.length+1 := by
  rw [(unitIntervalQueryRepresentation w S T s).adjacency,
    unitIntervalQuery_left_integer,unitIntervalQuery_left_integer]
  change (u≠v ∧ (Set.Icc (unitQueryLeftInteger w u : ℚ)
      ((unitQueryLeftInteger w u : ℚ)+(commonLength (2*p) w.length : ℚ)) ∩
    Set.Icc (unitQueryLeftInteger w v : ℚ)
      ((unitQueryLeftInteger w v : ℚ)+(commonLength (2*p) w.length : ℚ))).Nonempty) ↔ _
  have hL : (0 : ℚ) ≤ commonLength (2*p) w.length := by
    exact_mod_cast (commonLength_positive (2*p) w.length).le
  rw [icc_overlap (by linarith) (by linarith)]
  apply and_congr_right
  intro _
  rw [abs_lt]
  constructor
  · rintro ⟨hu,hv⟩
    have hu' : unitQueryLeftInteger w u≤unitQueryLeftInteger w v+commonLength (2*p) w.length := by
      exact_mod_cast hu
    have hv' : unitQueryLeftInteger w v≤unitQueryLeftInteger w u+commonLength (2*p) w.length := by
      exact_mod_cast hv
    omega
  · rintro ⟨hu,hv⟩
    constructor
    · exact_mod_cast (show unitQueryLeftInteger w u≤unitQueryLeftInteger w v+commonLength (2*p) w.length by omega)
    · exact_mod_cast (show unitQueryLeftInteger w v≤unitQueryLeftInteger w u+commonLength (2*p) w.length by omega)

end HiddenCircuits.GraphReduction
