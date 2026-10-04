import HiddenCircuits.GraphReduction.UnitIntervalGeometry

/-! Exact overlap classification for the even/odd layer coordinates. -/
namespace HiddenCircuits.GraphReduction.UnitInterval

theorem sameParity_overlap {Λ a b : ℚ} (hΛ : 0 < Λ)
    (ha : 0 < a ∧ a < Λ) (hb : 0 < b ∧ b < Λ) (r s e : ℤ) :
    (interval Λ (2*r+e) a ∩ interval Λ (2*s+e) b).Nonempty ↔ r=s := by
  constructor
  · intro hh
    by_contra hrs
    rcases lt_or_gt_of_ne hrs with h|h
    · exact separated hΛ ha.1 ha.2 hb.1 hb.2 (by omega) hh
    · rw [Set.inter_comm] at hh
      exact separated hΛ hb.1 hb.2 ha.1 ha.2 (by omega) hh
  · rintro rfl
    exact same_layer hΛ ha.1 ha.2 hb.1 hb.2 _

theorem evenOdd_overlap {Λ a b : ℚ} (hΛ : 0 < Λ)
    (ha : 0 < a ∧ a < Λ) (hb : 0 < b ∧ b < Λ) (r s : ℤ) :
    (interval Λ (2*r) a ∩ interval Λ (2*s+1) b).Nonempty ↔
      (r=s ∧ b ≤ a) ∨ (r=s+1 ∧ a ≤ b) := by
  by_cases hrs : r=s
  · subst s
    rw [consecutive hΛ ha.1 ha.2 hb.1 hb.2]
    simp
  · by_cases hrs' : r=s+1
    · subst r
      rw [Set.inter_comm]
      have he : 2*(s+1)=(2*s+1)+1 := by ring
      rw [he,consecutive hΛ hb.1 hb.2 ha.1 ha.2]
      simp
    · have hno : ¬(interval Λ (2*r) a ∩ interval Λ (2*s+1) b).Nonempty := by
        by_cases h : r<s
        · exact separated hΛ ha.1 ha.2 hb.1 hb.2 (by omega)
        · rw [Set.inter_comm]
          exact separated hΛ hb.1 hb.2 ha.1 ha.2 (by omega)
      simp [hno,hrs,hrs']

end HiddenCircuits.GraphReduction.UnitInterval
