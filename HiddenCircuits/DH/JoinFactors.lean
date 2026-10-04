import HiddenCircuits.DH.JoinBoundary
import HiddenCircuits.DH.BagBounds
import HiddenCircuits.DH.PartialPairs

/-! Independent crossing choices on the actual uncovered vertices of two bag matchings. -/
namespace HiddenCircuits.DH
open scoped BigOperators
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable {T : Set V} {U : Set W}

private def liftOption {A : Type*} (P : A → Prop) (o : Option A)
    (h : ∀ a, o = some a → P a) : Option {a // P a} :=
  match ho : o with
  | none => none
  | some a => some ⟨a, h a rfl⟩

private lemma liftOption_some_iff {A : Type*} (P : A → Prop) (o : Option A)
    (h : ∀ a, o = some a → P a) (a : {a // P a}) :
    liftOption P o h = some a ↔ o = some a.val := by
  cases o <;> simp [liftOption, Subtype.ext_iff]

private lemma liftOption_map {A : Type*} (P : A → Prop) (o : Option A)
    (h : ∀ a, o = some a → P a) :
    (liftOption P o h).map Subtype.val = o := by
  cases o <;> rfl

namespace JoinData
/-- Read the crossing edges as a partial bijection of the children's uncovered vertices. -/
def crossingPairs (d : JoinData G H T U) : PartialPairs (Unmatched d.left) (Unmatched d.right) where
  left v := liftOption (fun w => d.right.val w = none) (d.acrossLeft v.val)
    (fun w hw => (d.across_valid v.val w hw).2.1)
  right w := liftOption (fun v => d.left.val v = none) (d.acrossRight w.val)
    (fun v hv => (d.across_valid v w.val ((d.across_symm v w.val).mpr hv)).1)
  symm v w := by
    rw [liftOption_some_iff, liftOption_some_iff]
    exact d.across_symm _ _

@[simp] lemma crossingPairs_left_map (d : JoinData G H T U) (v : Unmatched d.left) :
    ((d.crossingPairs).left v).map Subtype.val = d.acrossLeft v.val := liftOption_map _ _ _

@[simp] lemma crossingPairs_right_map (d : JoinData G H T U) (w : Unmatched d.right) :
    ((d.crossingPairs).right w).map Subtype.val = d.acrossRight w.val := liftOption_map _ _ _

lemma crossingPairs_left_some (d : JoinData G H T U)
    (v : Unmatched d.left) (w : Unmatched d.right) :
    (d.crossingPairs).left v = some w ↔ d.acrossLeft v.val = some w.val :=
  liftOption_some_iff _ _ _ _

lemma crossingPairs_right_some (d : JoinData G H T U)
    (w : Unmatched d.right) (v : Unmatched d.left) :
    (d.crossingPairs).right w = some v ↔ d.acrossRight w.val = some v.val :=
  liftOption_some_iff _ _ _ _
end JoinData

/-- Extend crossing choices on uncovered vertices by absence on already covered vertices. -/
noncomputable def joinOfPairs (p : EncodedMatching G) (q : EncodedMatching H)
    (hp : Admissible T p) (hq : Admissible U q)
    (c : PartialPairs (Unmatched p) (Unmatched q)) : JoinData G H T U := by
  classical
  refine {
    left := p
    right := q
    acrossLeft := fun v => if hv : p.val v = none then (c.left ⟨v,hv⟩).map Subtype.val else none
    acrossRight := fun w => if hw : q.val w = none then (c.right ⟨w,hw⟩).map Subtype.val else none
    across_symm := ?_
    across_valid := ?_ }
  · intro v w
    constructor
    · intro h
      split_ifs at h with hv
      obtain ⟨w', hw', he⟩ := Option.map_eq_some_iff.mp h
      have hw : q.val w = none := he ▸ w'.property
      rw [dif_pos hw]
      have hcw : c.right w' = some ⟨v,hv⟩ := (c.symm _ _).mp hw'
      have hew : w' = ⟨w,hw⟩ := Subtype.ext he
      rw [← hew, hcw]
      rfl
    · intro h
      split_ifs at h with hw
      obtain ⟨v', hv', he⟩ := Option.map_eq_some_iff.mp h
      have hv : p.val v = none := he ▸ v'.property
      rw [dif_pos hv]
      have hcv : c.left v' = some ⟨w,hw⟩ := (c.symm _ _).mpr hv'
      have hev : v' = ⟨v,hv⟩ := Subtype.ext he
      rw [← hev, hcv]
      rfl
  · intro v w h
    split_ifs at h with hv
    obtain ⟨w', hw', he⟩ := Option.map_eq_some_iff.mp h
    have hw : q.val w = none := he ▸ w'.property
    exact ⟨hv, hw, hp v hv, hq w hw⟩

@[simp] lemma joinOfPairs_left (p : EncodedMatching G) (q : EncodedMatching H)
    (hp : Admissible T p) (hq : Admissible U q)
    (c : PartialPairs (Unmatched p) (Unmatched q)) :
    (joinOfPairs p q hp hq c).left = p := rfl

@[simp] lemma joinOfPairs_right (p : EncodedMatching G) (q : EncodedMatching H)
    (hp : Admissible T p) (hq : Admissible U q)
    (c : PartialPairs (Unmatched p) (Unmatched q)) :
    (joinOfPairs p q hp hq c).right = q := rfl

lemma crossingPairs_joinOfPairs (p : EncodedMatching G) (q : EncodedMatching H)
    (hp : Admissible T p) (hq : Admissible U q)
    (c : PartialPairs (Unmatched p) (Unmatched q)) :
    (joinOfPairs p q hp hq c).crossingPairs = c := by
  classical
  apply PartialPairs.ext_left
  funext v
  apply Option.ext
  intro w
  rw [JoinData.crossingPairs_left_some]
  change (if hv : p.val v.val = none then (c.left ⟨v.val,hv⟩).map Subtype.val else none) =
    some w.val ↔ _
  have hv : p.val v.val = none := v.property
  rw [dif_pos hv]
  simp only [Option.map_eq_some_iff]
  constructor
  · rintro ⟨w', hw', he⟩
    have hew : w' = w := Subtype.ext he
    simpa only [hew] using hw'
  · intro h
    exact ⟨w,h,rfl⟩

lemma joinOfPairs_crossingPairs (d : JoinData G H T U)
    (hl : Admissible T d.left) (hr : Admissible U d.right) :
    joinOfPairs d.left d.right hl hr d.crossingPairs = d := by
  classical
  apply JoinData.ext
  · rfl
  · rfl
  · funext v
    change (if hv : d.left.val v = none then
      ((d.crossingPairs).left ⟨v,hv⟩).map Subtype.val else none) = _
    split_ifs with hv
    · exact d.crossingPairs_left_map _
    · cases hc : d.acrossLeft v with
      | none => rfl
      | some w => exact (hv (d.across_valid v w hc).1).elim
  · funext w
    change (if hw : d.right.val w = none then
      ((d.crossingPairs).right ⟨w,hw⟩).map Subtype.val else none) = _
    split_ifs with hw
    · exact d.crossingPairs_right_map _
    · cases hc : d.acrossRight w with
      | none => rfl
      | some v => exact (hw (d.across_valid v w ((d.across_symm v w).mpr hc)).2.1).elim

/-- A matching satisfying a bag's active-boundary condition, before fixing its index. -/
def ActiveMatching (G : SimpleGraph V) (T : Set V) :=
  {p : EncodedMatching G // Admissible T p}

noncomputable instance [Fintype V] : Fintype (ActiveMatching G T) := by
  classical
  unfold ActiveMatching
  infer_instance

abbrev JoinFactors (G : SimpleGraph V) (H : SimpleGraph W) (T : Set V) (U : Set W) :=
  Σ p : ActiveMatching G T, Σ q : ActiveMatching H U,
    PartialPairs (Unmatched p.val) (Unmatched q.val)

/-- Crossing choices are independent once the two old graph matchings have been selected. -/
noncomputable def joinFactorsEquiv :
    {d : JoinData G H T U // Admissible T d.left ∧ Admissible U d.right} ≃
      JoinFactors G H T U where
  toFun d := ⟨⟨d.val.left,d.property.1⟩,⟨d.val.right,d.property.2⟩,d.val.crossingPairs⟩
  invFun x := ⟨joinOfPairs x.1.val x.2.1.val x.1.property x.2.1.property x.2.2,
    x.1.property,x.2.1.property⟩
  left_inv d := Subtype.ext (joinOfPairs_crossingPairs d.val d.property.1 d.property.2)
  right_inv x := by
    rcases x with ⟨p,q,c⟩
    simp only [crossingPairs_joinOfPairs]
    rfl

namespace JoinData
noncomputable def crossingDomainEquiv [Fintype V] [Fintype W] (d : JoinData G H T U) :
    d.crossingPairs.leftDomain ≃ {v : V // d.acrossLeft v ≠ none} where
  toFun v := ⟨v.val.val, by
    obtain ⟨w, hw⟩ := (d.crossingPairs.mem_leftDomain v.val).mp v.property
    have he := (d.crossingPairs_left_some v.val w).mp hw
    simp [he]⟩
  invFun v := by
    have hv : ∃ w, d.acrossLeft v.val = some w := Option.ne_none_iff_exists'.mp v.property
    have hp : d.left.val v.val = none := (d.across_valid v.val hv.choose hv.choose_spec).1
    have hq : d.right.val hv.choose = none := (d.across_valid v.val hv.choose hv.choose_spec).2.1
    exact ⟨⟨v.val,hp⟩, (d.crossingPairs.mem_leftDomain _).mpr
      ⟨⟨hv.choose,hq⟩, (d.crossingPairs_left_some _ _).mpr hv.choose_spec⟩⟩
  left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

/-- The graph-level number of crossing edges agrees with the independent choice's rank. -/
lemma crossingPairs_rank [Fintype V] [Fintype W] (d : JoinData G H T U) :
    d.crossingPairs.rank = d.crossingCount := by
  classical
  have h := Fintype.card_congr d.crossingDomainEquiv
  rw [Fintype.card_coe, Fintype.card_subtype] at h
  rw [PartialPairs.rank, h]
  unfold crossingCount
  simpa only [Nat.cast_id, ite_not] using
    (Finset.sum_boole (R := ℕ) (fun v => d.acrossLeft v ≠ none) Finset.univ).symm

lemma crossingPairs_fullRight_iff [Fintype V] [Fintype W] (d : JoinData G H T U) :
    d.crossingPairs.FullRight ↔
      (∀ w, d.right.val w = none → d.acrossRight w ≠ none) := by
  constructor
  · intro h w hw ha
    obtain ⟨v, hv⟩ := h ⟨w,hw⟩
    have he := (d.crossingPairs_right_some ⟨w,hw⟩ v).mp hv
    simp [ha] at he
  · intro h w
    obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp (h w.val w.property)
    have hp := (d.across_valid v w.val ((d.across_symm v w.val).mpr hv)).1
    exact ⟨⟨v,hp⟩, (d.crossingPairs_right_some _ _).mpr hv⟩
end JoinData

end HiddenCircuits.DH
