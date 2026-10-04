import Mathlib.Tactic

/-! Actual equal-length closed interval geometry for Section 10. -/
namespace HiddenCircuits.GraphReduction.UnitInterval

def interval (Λ : ℚ) (j : ℤ) (a : ℚ) : Set ℚ :=
  Set.Icc ((j : ℚ)*Λ+a) (((j : ℚ)+1)*Λ+a)

def probe (Λ : ℚ) (j : ℤ) : Set ℚ :=
  Set.Icc (((2*j+1 : ℤ) : ℚ)*Λ) (((2*j+2 : ℤ) : ℚ)*Λ)

theorem icc_overlap {a b c d : ℚ} (hab : a ≤ b) (hcd : c ≤ d) :
    (Set.Icc a b ∩ Set.Icc c d).Nonempty ↔ a ≤ d ∧ c ≤ b := by
  constructor
  · rintro ⟨x,⟨hax,hxb⟩,⟨hcx,hxd⟩⟩
    exact ⟨hax.trans hxd,hcx.trans hxb⟩
  · rintro ⟨had,hcb⟩
    exact ⟨max a c,⟨le_max_left _ _,max_le hab hcb⟩,
      ⟨le_max_right _ _,max_le had hcd⟩⟩

theorem overlap_iff {Λ : ℚ} (hΛ : 0 ≤ Λ) (j k : ℤ) (a b : ℚ) :
    (interval Λ j a ∩ interval Λ k b).Nonempty ↔
    (j:ℚ)*Λ+a ≤ ((k:ℚ)+1)*Λ+b ∧ (k:ℚ)*Λ+b ≤ ((j:ℚ)+1)*Λ+a := by
  apply icc_overlap <;> nlinarith

theorem same_layer {Λ a b : ℚ} (hΛ : 0 < Λ) (ha : 0 < a) (ha' : a < Λ)
    (hb : 0 < b) (hb' : b < Λ) (j : ℤ) :
    (interval Λ j a ∩ interval Λ j b).Nonempty := by
  rw [overlap_iff hΛ.le]; constructor <;> nlinarith

theorem consecutive {Λ a b : ℚ} (hΛ : 0 < Λ) (ha : 0 < a) (ha' : a < Λ)
    (hb : 0 < b) (hb' : b < Λ) (j : ℤ) :
    (interval Λ j a ∩ interval Λ (j+1) b).Nonempty ↔ b ≤ a := by
  rw [overlap_iff hΛ.le]
  push_cast
  constructor
  · intro h; nlinarith [h.2]
  · intro h; constructor <;> nlinarith

theorem separated {Λ a b : ℚ} (hΛ : 0 < Λ) (ha : 0 < a) (ha' : a < Λ)
    (hb : 0 < b) (hb' : b < Λ) {j k : ℤ} (hjk : j+2 ≤ k) :
    ¬(interval Λ j a ∩ interval Λ k b).Nonempty := by
  rw [overlap_iff hΛ.le]
  have h : (j:ℚ)+2 ≤ (k:ℚ) := by exact_mod_cast hjk
  intro hh
  have := mul_le_mul_of_nonneg_right h hΛ.le
  nlinarith [hh.2]

theorem probe_original {Λ a : ℚ} (hΛ : 0 < Λ) (ha : 0 < a) (ha' : a < Λ)
    (j k : ℤ) :
    (probe Λ j ∩ interval Λ k a).Nonempty ↔ k=2*j ∨ k=2*j+1 := by
  unfold probe interval
  rw [icc_overlap (by push_cast; nlinarith) (by nlinarith)]
  push_cast
  constructor
  · intro h
    have hlo : 2*j ≤ k := by
      by_contra hn
      have hk : (k:ℚ)+1 ≤ 2*(j:ℚ) := by exact_mod_cast (show k+1 ≤ 2*j by omega)
      have := mul_le_mul_of_nonneg_right hk hΛ.le
      nlinarith [h.1]
    have hhi : k ≤ 2*j+1 := by
      by_contra hn
      have hk : 2*(j:ℚ)+2 ≤ (k:ℚ) := by exact_mod_cast (show 2*j+2 ≤ k by omega)
      have := mul_le_mul_of_nonneg_right hk hΛ.le
      nlinarith [h.2]
    omega
  · rintro (rfl|rfl) <;> push_cast <;> constructor <;> nlinarith

theorem probe_self {Λ : ℚ} (hΛ : 0 < Λ) (j : ℤ) :
    (probe Λ j ∩ probe Λ j).Nonempty := by
  unfold probe
  rw [icc_overlap (by push_cast; nlinarith) (by push_cast; nlinarith)]
  constructor <;> push_cast <;> nlinarith

theorem probes_separated {Λ : ℚ} (hΛ : 0 < Λ) {j k : ℤ} (hjk : j ≠ k) :
    ¬(probe Λ j ∩ probe Λ k).Nonempty := by
  unfold probe
  rw [icc_overlap (by push_cast; nlinarith) (by push_cast; nlinarith)]
  push_cast
  intro h
  rcases lt_or_gt_of_ne hjk with hjk|hkj
  · have hk : (j:ℚ)+1 ≤ (k:ℚ) := by exact_mod_cast (show j+1 ≤ k by omega)
    have := mul_le_mul_of_nonneg_right hk hΛ.le
    nlinarith [h.2]
  · have hj : (k:ℚ)+1 ≤ (j:ℚ) := by exact_mod_cast (show k+1 ≤ j by omega)
    have := mul_le_mul_of_nonneg_right hj hΛ.le
    nlinarith [h.1]

end HiddenCircuits.GraphReduction.UnitInterval
