import HiddenCircuits.DH.StateFibers

/-! Cardinal formulas for actual graph bag matchings, obtained from independent crossing fibers. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable {T : Set V} {U : Set W}

noncomputable def joinFactorsFiberEquiv
    (P : (p : EncodedMatching G) → (q : EncodedMatching H) →
      PartialPairs (Unmatched p) (Unmatched q) → Prop) :
    {d : JoinData G H T U // Admissible T d.left ∧ Admissible U d.right ∧
      P d.left d.right d.crossingPairs} ≃
    (Σ p : ActiveMatching G T, Σ q : ActiveMatching H U,
      {c : PartialPairs (Unmatched p.val) (Unmatched q.val) // P p.val q.val c}) where
  toFun d := ⟨⟨d.val.left,d.property.1⟩,⟨d.val.right,d.property.2.1⟩,
    ⟨d.val.crossingPairs,d.property.2.2⟩⟩
  invFun x := ⟨joinOfPairs x.1.val x.2.1.val x.1.property x.2.1.property x.2.2.val,
    x.1.property,x.2.1.property,by
      simpa only [joinOfPairs_left,joinOfPairs_right,crossingPairs_joinOfPairs] using x.2.2.property⟩
  left_inv d := Subtype.ext (joinOfPairs_crossingPairs d.val d.property.1 d.property.2.1)
  right_inv x := by
    rcases x with ⟨p,q,c⟩
    simp only [crossingPairs_joinOfPairs]
    rfl

/-- Actual true-twin states as independent child matchings and a rank-constrained partial bijection. -/
noncomputable def trueTwinFactorsEquiv [Fintype V] [Fintype W] (k : ℕ) :
    BagState (joinGraph G H T U) {x | Sum.elim T U x} k ≃
    (Σ p : ActiveMatching G T, Σ q : ActiveMatching H U,
      {c : PartialPairs (Unmatched p.val) (Unmatched q.val) //
        uncovered p.val + uncovered q.val = k + 2*c.rank}) :=
  (trueTwinStateEquiv k).trans ((Equiv.subtypeEquivRight (by
    intro d
    rw [d.crossingPairs_rank])).trans
      (joinFactorsFiberEquiv (fun p q c => uncovered p + uncovered q = k + 2*c.rank)))

/-- Actual pendant states as independent child matchings and full absorbed-side coverage. -/
noncomputable def pendantFactorsEquiv [Fintype V] [Fintype W] (k : ℕ) :
    BagState (joinGraph G H T U) {x | ∃ v ∈ T, x = Sum.inl v} k ≃
    (Σ p : ActiveMatching G T, Σ q : ActiveMatching H U,
      {c : PartialPairs (Unmatched p.val) (Unmatched q.val) //
        c.FullRight ∧ uncovered p.val = k + uncovered q.val}) :=
  (pendantStateEquiv k).trans ((Equiv.subtypeEquivRight (by
    intro d
    rw [d.crossingPairs_fullRight_iff])).trans
      (joinFactorsFiberEquiv (fun p q c => c.FullRight ∧ uncovered p = k + uncovered q)))

/-- Exact pendant multiplicity for each pair of actual internal matchings. -/
theorem pendantFiber_card [Fintype V] [Fintype W]
    (p : EncodedMatching G) (q : EncodedMatching H) (k : ℕ) :
    Fintype.card {c : PartialPairs (Unmatched p) (Unmatched q) //
      c.FullRight ∧ uncovered p = k + uncovered q} =
    if uncovered p = k + uncovered q then (uncovered p).descFactorial (uncovered q) else 0 := by
  classical
  by_cases he : uncovered p = k + uncovered q
  · rw [if_pos he]
    let e : {c : PartialPairs (Unmatched p) (Unmatched q) //
        c.FullRight ∧ uncovered p = k + uncovered q} ≃
        {c : PartialPairs (Unmatched p) (Unmatched q) // c.FullRight} :=
      Equiv.subtypeEquivRight (fun _ => by simp only [he, and_true])
    rw [Fintype.card_congr e,PartialPairs.fullRight_card,unmatched_card,unmatched_card]
  · rw [if_neg he]
    haveI : IsEmpty {c : PartialPairs (Unmatched p) (Unmatched q) //
        c.FullRight ∧ uncovered p = k + uncovered q} := ⟨fun c => he c.property.2⟩
    exact Fintype.card_eq_zero

/-- A genuine pendant graph-state counting identity, before grouping equal child indices. -/
theorem pendant_count_matchings [Fintype V] [Fintype W] (k : ℕ) :
    Fintype.card (BagState (joinGraph G H T U) {x | ∃ v ∈ T, x = Sum.inl v} k) =
    ∑ p : ActiveMatching G T, ∑ q : ActiveMatching H U,
      if uncovered p.val = k + uncovered q.val then
        (uncovered p.val).descFactorial (uncovered q.val) else 0 := by
  classical
  rw [Fintype.card_congr (pendantFactorsEquiv k)]
  simp only [Fintype.card_sigma,pendantFiber_card]

/-- Exact true-twin multiplicities for any fixed pair of actual child matchings. -/
theorem trueTwinFiber_card [Fintype V] [Fintype W]
    (p : EncodedMatching G) (q : EncodedMatching H) (k : ℕ) :
    Fintype.card {c : PartialPairs (Unmatched p) (Unmatched q) //
      uncovered p + uncovered q = k + 2*c.rank} =
    ∑ r : Fin (Fintype.card V+1),
      if uncovered p + uncovered q = k + 2*r.val then
        (uncovered p).choose r.val * (uncovered q).choose r.val * r.val.factorial else 0 := by
  classical
  simpa only [unmatched_card] using
    (PartialPairs.rankFilter_card (V := Unmatched p) (W := Unmatched q) (Fintype.card V)
      (fun c => c.rank_le_card.trans (by rw [unmatched_card]; exact uncovered_le_card p))
      (fun r => uncovered p + uncovered q = k + 2*r))

/-- The true-twin count before collecting child matchings with equal state indices. -/
theorem trueTwin_count_matchings [Fintype V] [Fintype W] (k : ℕ) :
    Fintype.card (BagState (joinGraph G H T U) {x | Sum.elim T U x} k) =
    ∑ p : ActiveMatching G T, ∑ q : ActiveMatching H U,
      ∑ r : Fin (Fintype.card V+1),
        if uncovered p.val + uncovered q.val = k + 2*r.val then
          (uncovered p.val).choose r.val * (uncovered q.val).choose r.val * r.val.factorial else 0 := by
  classical
  rw [Fintype.card_congr (trueTwinFactorsEquiv k)]
  simp only [Fintype.card_sigma,trueTwinFiber_card]

/-- The pendant array update counts precisely the genuine merged graph states. -/
theorem pendant_count [Fintype V] [Fintype W] (k : ℕ) :
    Fintype.card (BagState (joinGraph G H T U) {x | ∃ v ∈ T, x = Sum.inl v} k) =
    ∑ i : Fin (Fintype.card V+1), ∑ j : Fin (Fintype.card W+1),
      if i.val = k+j.val then
        Fintype.card (BagState G T i.val) * Fintype.card (BagState H U j.val) *
          i.val.descFactorial j.val else 0 := by
  classical
  rw [pendant_count_matchings]
  have hq (p : ActiveMatching G T) :
      (∑ q : ActiveMatching H U, if uncovered p.val = k+uncovered q.val then
        (uncovered p.val).descFactorial (uncovered q.val) else 0) =
      ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val) *
        (if uncovered p.val = k+j.val then (uncovered p.val).descFactorial j.val else 0) :=
    sum_activeMatching (fun j => if uncovered p.val = k+j then
      (uncovered p.val).descFactorial j else 0)
  simp_rw [hq]
  rw [sum_activeMatching (G := G) (T := T)
    (fun i => ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val) *
      (if i = k+j.val then i.descFactorial j.val else 0))]
  simp only [Finset.mul_sum,mul_ite,mul_zero,mul_assoc]

/-- The true-twin array update counts precisely the genuine merged graph states.
The fixed finite ranges include zero binomial terms beyond min(i,j). -/
theorem trueTwin_count [Fintype V] [Fintype W] (k : ℕ) :
    Fintype.card (BagState (joinGraph G H T U) {x | Sum.elim T U x} k) =
    ∑ i : Fin (Fintype.card V+1), ∑ j : Fin (Fintype.card W+1),
      ∑ r : Fin (Fintype.card V+1),
        if i.val+j.val = k+2*r.val then
          Fintype.card (BagState G T i.val) * Fintype.card (BagState H U j.val) *
            (i.val.choose r.val * j.val.choose r.val * r.val.factorial) else 0 := by
  classical
  rw [trueTwin_count_matchings]
  have hq (p : ActiveMatching G T) :
      (∑ q : ActiveMatching H U, ∑ r : Fin (Fintype.card V+1),
        if uncovered p.val+uncovered q.val = k+2*r.val then
          (uncovered p.val).choose r.val * (uncovered q.val).choose r.val * r.val.factorial else 0) =
      ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val) *
        ∑ r : Fin (Fintype.card V+1), if uncovered p.val+j.val = k+2*r.val then
          (uncovered p.val).choose r.val * j.val.choose r.val * r.val.factorial else 0 :=
    sum_activeMatching (fun j => ∑ r : Fin (Fintype.card V+1),
      if uncovered p.val+j = k+2*r.val then
        (uncovered p.val).choose r.val * j.choose r.val * r.val.factorial else 0)
  simp_rw [hq]
  rw [sum_activeMatching (G := G) (T := T)
    (fun i => ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val) *
      ∑ r : Fin (Fintype.card V+1), if i+j.val = k+2*r.val then
        i.choose r.val * j.val.choose r.val * r.val.factorial else 0)]
  simp only [Finset.mul_sum,mul_ite,mul_zero,mul_assoc]

/-- The same crossing fiber, indexed only up to the absorbed child's exposed count. -/
theorem trueTwinFiber_card_right [Fintype V] [Fintype W]
    (p : EncodedMatching G) (q : EncodedMatching H) (k : ℕ) :
    Fintype.card {c : PartialPairs (Unmatched p) (Unmatched q) //
      uncovered p + uncovered q = k + 2*c.rank} =
    ∑ r : Fin (uncovered q+1),
      if uncovered p + uncovered q = k + 2*r.val then
        (uncovered p).choose r.val * (uncovered q).choose r.val * r.val.factorial else 0 := by
  classical
  simpa only [unmatched_card] using
    (PartialPairs.rankFilter_card (V := Unmatched p) (W := Unmatched q) (uncovered q)
      (fun c => c.rank_le_card_right.trans_eq (unmatched_card q))
      (fun r => uncovered p + uncovered q = k + 2*r))

/-- Equivalent true-twin formula with the inner range 0≤r≤j, suited to Q_j. -/
theorem trueTwin_count_rightRange [Fintype V] [Fintype W] (k : ℕ) :
    Fintype.card (BagState (joinGraph G H T U) {x | Sum.elim T U x} k) =
    ∑ i : Fin (Fintype.card V+1), ∑ j : Fin (Fintype.card W+1),
      ∑ r : Fin (j.val+1),
        if i.val+j.val = k+2*r.val then
          Fintype.card (BagState G T i.val) * Fintype.card (BagState H U j.val) *
            (i.val.choose r.val * j.val.choose r.val * r.val.factorial) else 0 := by
  classical
  rw [Fintype.card_congr (trueTwinFactorsEquiv k)]
  simp only [Fintype.card_sigma,trueTwinFiber_card_right]
  have hq (p : ActiveMatching G T) :
      (∑ q : ActiveMatching H U, ∑ r : Fin (uncovered q.val+1),
        if uncovered p.val+uncovered q.val = k+2*r.val then
          (uncovered p.val).choose r.val * (uncovered q.val).choose r.val * r.val.factorial else 0) =
      ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val) *
        ∑ r : Fin (j.val+1), if uncovered p.val+j.val = k+2*r.val then
          (uncovered p.val).choose r.val * j.val.choose r.val * r.val.factorial else 0 :=
    sum_activeMatching (fun j => ∑ r : Fin (j+1),
      if uncovered p.val+j = k+2*r.val then
        (uncovered p.val).choose r.val * j.choose r.val * r.val.factorial else 0)
  simp_rw [hq]
  rw [sum_activeMatching (G := G) (T := T)
    (fun i => ∑ j : Fin (Fintype.card W+1), Fintype.card (BagState H U j.val) *
      ∑ r : Fin (j.val+1), if i+j.val = k+2*r.val then
        i.choose r.val * j.val.choose r.val * r.val.factorial else 0)]
  simp only [Finset.mul_sum,mul_ite,mul_zero,mul_assoc]

end HiddenCircuits.DH
