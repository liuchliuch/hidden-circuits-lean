import HiddenCircuits.DH.JoinMatching

/-! Restrict the graph-level join bijection to the exact twin and pendant bag states. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable {T : Set V} {U : Set W}

namespace JoinData
lemma partner_inl_none (d : JoinData G H T U) (v : V) :
    d.partner (.inl v) = none ↔ d.left.val v = none ∧ d.acrossLeft v = none := by
  simp only [partner]
  cases d.left.val v <;> simp

lemma partner_inr_none (d : JoinData G H T U) (w : W) :
    d.partner (.inr w) = none ↔ d.right.val w = none ∧ d.acrossRight w = none := by
  simp only [partner]
  cases d.right.val w <;> simp

lemma twin_admissible_iff (d : JoinData G H T U) :
    Admissible {x | Sum.elim T U x} d.matching ↔
      Admissible T d.left ∧ Admissible U d.right := by
  constructor
  · intro h
    constructor
    · intro v hv
      cases ha : d.acrossLeft v with
      | none => exact h (.inl v) ((d.partner_inl_none v).mpr ⟨hv, ha⟩)
      | some w => exact (d.across_valid v w ha).2.2.1
    · intro w hw
      cases ha : d.acrossRight w with
      | none => exact h (.inr w) ((d.partner_inr_none w).mpr ⟨hw, ha⟩)
      | some v => exact (d.across_valid v w ((d.across_symm v w).mpr ha)).2.2.2
  · rintro ⟨hl, hr⟩ x hx
    cases x with
    | inl v => exact hl v ((d.partner_inl_none v).mp hx).1
    | inr w => exact hr w ((d.partner_inr_none w).mp hx).1

/-- The absorbed side must be entirely covered; the surviving side remains active. -/
lemma pendant_admissible_iff (d : JoinData G H T U) :
    Admissible {x | ∃ v ∈ T, x = Sum.inl v} d.matching ↔
      Admissible T d.left ∧ Admissible U d.right ∧
      (∀ w, d.right.val w = none → d.acrossRight w ≠ none) := by
  constructor
  · intro h
    have ht : Admissible {x | Sum.elim T U x} d.matching := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := h x hx
      exact hv
    obtain ⟨hl, hr⟩ := d.twin_admissible_iff.mp ht
    refine ⟨hl, hr, ?_⟩
    intro w hw ha
    obtain ⟨v, hv, he⟩ := h (.inr w) ((d.partner_inr_none w).mpr ⟨hw, ha⟩)
    cases he
  · rintro ⟨hl, hr, hc⟩ x hx
    cases x with
    | inl v => exact ⟨v, hl v ((d.partner_inl_none v).mp hx).1, rfl⟩
    | inr w => exact (hc w ((d.partner_inr_none w).mp hx).1
        ((d.partner_inr_none w).mp hx).2).elim

noncomputable def crossingCount [Fintype V] (d : JoinData G H T U) : ℕ := by
  classical
  exact ∑ v, if d.acrossLeft v = none then 0 else 1

lemma crossingCount_eq_right [Fintype V] [Fintype W] (d : JoinData G H T U) :
    d.crossingCount = ∑ w, if d.acrossRight w = none then 0 else 1 := by
  classical
  have hl (v : V) : (if d.acrossLeft v = none then 0 else 1) =
      ∑ w, if d.acrossLeft v = some w then 1 else 0 := by
    cases h : d.acrossLeft v <;> simp [h]
  have hr (w : W) : (if d.acrossRight w = none then 0 else 1) =
      ∑ v, if d.acrossRight w = some v then 1 else 0 := by
    cases h : d.acrossRight w <;> simp [h]
  unfold crossingCount
  simp_rw [hl, hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  simp only [d.across_symm]

/-- Each crossing edge removes exactly one uncovered vertex from each child. -/
lemma uncovered_conservation [Fintype V] [Fintype W] (d : JoinData G H T U) :
    uncovered d.matching + 2 * d.crossingCount = uncovered d.left + uncovered d.right := by
  classical
  have hl (v : V) :
      (if d.partner (.inl v) = none then 1 else 0) +
      (if d.acrossLeft v = none then 0 else 1) =
      (if d.left.val v = none then 1 else 0) := by
    cases hp : d.left.val v with
    | none => simp [partner_inl_none, hp]; split_ifs <;> omega
    | some v' =>
      have ha : d.acrossLeft v = none := by
        cases h : d.acrossLeft v with
        | none => rfl
        | some w => have := (d.across_valid v w h).1; simp [hp] at this
      simp [partner_inl_none, hp, ha]
  have hr (w : W) :
      (if d.partner (.inr w) = none then 1 else 0) +
      (if d.acrossRight w = none then 0 else 1) =
      (if d.right.val w = none then 1 else 0) := by
    cases hp : d.right.val w with
    | none => simp [partner_inr_none, hp]; split_ifs <;> omega
    | some w' =>
      have ha : d.acrossRight w = none := by
        cases h : d.acrossRight w with
        | none => rfl
        | some v =>
          have := (d.across_valid v w ((d.across_symm v w).mpr h)).2.1
          simp [hp] at this
      simp [partner_inr_none, hp, ha]
  have hl' := congrArg (fun f : V → ℕ => ∑ v, f v) (funext hl)
  have hr' := congrArg (fun f : W → ℕ => ∑ w, f w) (funext hr)
  simp only [Finset.sum_add_distrib] at hl' hr'
  have hc := d.crossingCount_eq_right
  unfold uncovered
  rw [Fintype.sum_sum_type]
  change _ + 2 * d.crossingCount = _
  change (∑ v, if d.partner (.inl v) = none then 1 else 0) +
    (∑ w, if d.partner (.inr w) = none then 1 else 0) + 2 * d.crossingCount = _
  change (∑ v, if d.partner (.inl v) = none then 1 else 0) + d.crossingCount = _ at hl'
  omega

lemma pendant_crossingCount [Fintype V] [Fintype W] (d : JoinData G H T U)
    (h : ∀ w, d.right.val w = none → d.acrossRight w ≠ none) :
    d.crossingCount = uncovered d.right := by
  classical
  rw [d.crossingCount_eq_right]
  unfold uncovered
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : d.right.val w = none
  · simp [hw, h w hw]
  · have ha : d.acrossRight w = none := by
      cases he : d.acrossRight w with
      | none => rfl
      | some v => exact (hw (d.across_valid v w ((d.across_symm v w).mpr he)).2.1).elim
    simp [hw, ha]
end JoinData

/-- Exact boundary-state bijection for a true-twin merge, including crossing-edge rank. -/
noncomputable def trueTwinStateEquiv [Fintype V] [Fintype W] (k : ℕ) :
    BagState (joinGraph G H T U) {x | Sum.elim T U x} k ≃
    {d : JoinData G H T U // Admissible T d.left ∧ Admissible U d.right ∧
      uncovered d.left + uncovered d.right = k + 2 * d.crossingCount} :=
  joinMatchingEquiv.subtypeEquiv (by
    intro m
    let d := decomposeJoin m
    have he : d.matching = m := matching_decomposeJoin m
    have ha := d.twin_admissible_iff
    have hc := d.uncovered_conservation
    rw [he] at ha hc
    change (Admissible _ m ∧ uncovered m = k) ↔ _
    change _ ↔ Admissible T d.left ∧ Admissible U d.right ∧
      uncovered d.left + uncovered d.right = k + 2 * d.crossingCount
    rw [ha]
    constructor
    · rintro ⟨⟨hl, hr⟩, hk⟩
      exact ⟨hl, hr, by omega⟩
    · rintro ⟨hl, hr, hk⟩
      exact ⟨⟨hl, hr⟩, by omega⟩)

/-- Exact pendant boundary-state bijection: every absorbed-side exposed vertex is paired. -/
noncomputable def pendantStateEquiv [Fintype V] [Fintype W] (k : ℕ) :
    BagState (joinGraph G H T U) {x | ∃ v ∈ T, x = Sum.inl v} k ≃
    {d : JoinData G H T U // Admissible T d.left ∧ Admissible U d.right ∧
      (∀ w, d.right.val w = none → d.acrossRight w ≠ none) ∧
      uncovered d.left = k + uncovered d.right} :=
  joinMatchingEquiv.subtypeEquiv (by
    intro m
    let d := decomposeJoin m
    have he : d.matching = m := matching_decomposeJoin m
    have ha := d.pendant_admissible_iff
    have hc := d.uncovered_conservation
    rw [he] at ha hc
    change (Admissible _ m ∧ uncovered m = k) ↔ _
    change _ ↔ Admissible T d.left ∧ Admissible U d.right ∧
      (∀ w, d.right.val w = none → d.acrossRight w ≠ none) ∧
      uncovered d.left = k + uncovered d.right
    rw [ha]
    constructor
    · rintro ⟨⟨hl, hr, hp⟩, hk⟩
      have hd := d.pendant_crossingCount hp
      exact ⟨hl, hr, hp, by omega⟩
    · rintro ⟨hl, hr, hp, hk⟩
      have hd := d.pendant_crossingCount hp
      exact ⟨⟨hl, hr, hp⟩, by omega⟩)

end HiddenCircuits.DH
