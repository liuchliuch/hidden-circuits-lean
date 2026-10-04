import HiddenCircuits.DH.BagMatching
import HiddenCircuits.DH.CrossPairs

/-! Genuine decomposition of graph matchings across a complete active bipartite block.
The factors are internal graph matchings and an independently specified partial bijection
between their uncovered active vertices. No matching-count identity is assumed. -/
namespace HiddenCircuits.DH
open SimpleGraph
open scoped BigOperators
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Two induced bags joined exactly along their active vertices. -/
def joinGraph (G : SimpleGraph V) (H : SimpleGraph W) (T : Set V) (U : Set W) :
    SimpleGraph (V ⊕ W) where
  Adj
    | .inl v, .inl w => G.Adj v w
    | .inr v, .inr w => H.Adj v w
    | .inl v, .inr w => v ∈ T ∧ w ∈ U
    | .inr w, .inl v => v ∈ T ∧ w ∈ U
  symm := by
    intro x y
    cases x <;> cases y <;> simp
    · exact G.adj_symm
    · exact H.adj_symm
  loopless := ⟨by intro x; cases x <;> simp⟩

variable {T : Set V} {U : Set W}

def joinLeft (m : EncodedMatching (joinGraph G H T U)) : EncodedMatching G := by
  refine ⟨fun v => leftOption (m.val (.inl v)), ?_, ?_⟩
  · intro v w h
    apply (leftOption_some_iff _ _).mpr
    exact m.property.1 _ _ ((leftOption_some_iff _ _).mp h)
  · intro v w h
    exact m.property.2 _ _ ((leftOption_some_iff _ _).mp h)

def joinRight (m : EncodedMatching (joinGraph G H T U)) : EncodedMatching H := by
  refine ⟨fun v => rightOption (m.val (.inr v)), ?_, ?_⟩
  · intro v w h
    apply (rightOption_some_iff _ _).mpr
    exact m.property.1 _ _ ((rightOption_some_iff _ _).mp h)
  · intro v w h
    exact m.property.2 _ _ ((rightOption_some_iff _ _).mp h)

/-- Independently specified internal matchings and compatible crossing partial bijection. -/
structure JoinData (G : SimpleGraph V) (H : SimpleGraph W) (T : Set V) (U : Set W) where
  left : EncodedMatching G
  right : EncodedMatching H
  acrossLeft : V → Option W
  acrossRight : W → Option V
  across_symm : ∀ v w, acrossLeft v = some w ↔ acrossRight w = some v
  across_valid : ∀ v w, acrossLeft v = some w →
    left.val v = none ∧ right.val w = none ∧ v ∈ T ∧ w ∈ U

namespace JoinData
@[ext] theorem ext {a b : JoinData G H T U} (hl : a.left = b.left)
    (hr : a.right = b.right) (hcl : a.acrossLeft = b.acrossLeft)
    (hcr : a.acrossRight = b.acrossRight) : a = b := by
  cases a; cases b; simp_all

def partner (d : JoinData G H T U) : V ⊕ W → Option (V ⊕ W)
  | .inl v => match d.left.val v with
    | some w => some (.inl w)
    | none => (d.acrossLeft v).map Sum.inr
  | .inr v => match d.right.val v with
    | some w => some (.inr w)
    | none => (d.acrossRight v).map Sum.inl

lemma partner_inl_left (d : JoinData G H T U) (v v' : V) :
    d.partner (.inl v) = some (.inl v') ↔ d.left.val v = some v' := by
  simp only [partner]
  cases d.left.val v <;> simp

lemma partner_inr_right (d : JoinData G H T U) (w w' : W) :
    d.partner (.inr w) = some (.inr w') ↔ d.right.val w = some w' := by
  simp only [partner]
  cases d.right.val w <;> simp

lemma partner_inl_right (d : JoinData G H T U) (v : V) (w : W) :
    d.partner (.inl v) = some (.inr w) ↔ d.acrossLeft v = some w := by
  cases h : d.left.val v with
  | none => simp [partner, h]
  | some v' =>
    simp only [partner, h, reduceCtorEq, Option.some.injEq, false_iff]
    intro he
    have := (d.across_valid v w he).1
    simp [h] at this

lemma partner_inr_left (d : JoinData G H T U) (w : W) (v : V) :
    d.partner (.inr w) = some (.inl v) ↔ d.acrossRight w = some v := by
  cases h : d.right.val w with
  | none => simp [partner, h]
  | some w' =>
    simp only [partner, h, reduceCtorEq, Option.some.injEq, false_iff]
    intro he
    have := (d.across_valid v w ((d.across_symm v w).mpr he)).2.1
    simp [h] at this

/-- Union of the internal and crossing edges is an actual graph matching. -/
def matching (d : JoinData G H T U) : EncodedMatching (joinGraph G H T U) := by
  refine ⟨d.partner, ?_, ?_⟩
  · intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl v' =>
        exact (d.partner_inl_left v' v).mpr
          (d.left.property.1 v v' ((d.partner_inl_left v v').mp h))
      | inr w =>
        exact (d.partner_inr_left w v).mpr
          ((d.across_symm v w).mp ((d.partner_inl_right v w).mp h))
    | inr w =>
      cases y with
      | inl v =>
        exact (d.partner_inl_right v w).mpr
          ((d.across_symm v w).mpr ((d.partner_inr_left w v).mp h))
      | inr w' =>
        exact (d.partner_inr_right w' w).mpr
          (d.right.property.1 w w' ((d.partner_inr_right w w').mp h))
  · intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl v' =>
        exact d.left.property.2 v v' ((d.partner_inl_left v v').mp h)
      | inr w =>
        exact (d.across_valid v w ((d.partner_inl_right v w).mp h)).2.2
    | inr w =>
      cases y with
      | inl v =>
        exact (d.across_valid v w
          ((d.across_symm v w).mpr ((d.partner_inr_left w v).mp h))).2.2
      | inr w' =>
        exact d.right.property.2 w w' ((d.partner_inr_right w w').mp h)
end JoinData

/-- Restrict an arbitrary matching to its two internal parts and its crossing edges. -/
def decomposeJoin (m : EncodedMatching (joinGraph G H T U)) : JoinData G H T U where
  left := joinLeft m
  right := joinRight m
  acrossLeft v := rightOption (m.val (.inl v))
  acrossRight w := leftOption (m.val (.inr w))
  across_symm v w := by
    rw [rightOption_some_iff, leftOption_some_iff]
    exact ⟨m.property.1 _ _, m.property.1 _ _⟩
  across_valid v w h := by
    have hv := (rightOption_some_iff _ _).mp h
    have hw := m.property.1 _ _ hv
    exact ⟨by simp [joinLeft, hv, leftOption],
      by simp [joinRight, hw, rightOption], m.property.2 _ _ hv⟩

lemma matching_decomposeJoin (m : EncodedMatching (joinGraph G H T U)) :
    (decomposeJoin m).matching = m := by
  apply Subtype.ext
  funext x
  cases x with
  | inl v =>
    change (match leftOption (m.val (.inl v)) with
      | some w => some (Sum.inl w)
      | none => (rightOption (m.val (.inl v))).map Sum.inr) = _
    cases m.val (.inl v) with
    | none => rfl
    | some w => cases w <;> rfl
  | inr w =>
    change (match rightOption (m.val (.inr w)) with
      | some v => some (Sum.inr v)
      | none => (leftOption (m.val (.inr w))).map Sum.inl) = _
    cases m.val (.inr w) with
    | none => rfl
    | some v => cases v <;> rfl

lemma decomposeJoin_matching (d : JoinData G H T U) :
    decomposeJoin d.matching = d := by
  apply JoinData.ext
  · apply Subtype.ext
    funext v
    apply Option.ext
    intro v'
    change leftOption (d.partner (.inl v)) = some v' ↔ _
    rw [leftOption_some_iff, d.partner_inl_left]
  · apply Subtype.ext
    funext w
    apply Option.ext
    intro w'
    change rightOption (d.partner (.inr w)) = some w' ↔ _
    rw [rightOption_some_iff, d.partner_inr_right]
  · funext v
    apply Option.ext
    intro w
    change rightOption (d.partner (.inl v)) = some w ↔ _
    rw [rightOption_some_iff, d.partner_inl_right]
  · funext w
    apply Option.ext
    intro v
    change leftOption (d.partner (.inr w)) = some v ↔ _
    rw [leftOption_some_iff, d.partner_inr_left]

/-- The cross-bag decomposition is a bijection, not merely an upper bound. -/
def joinMatchingEquiv : EncodedMatching (joinGraph G H T U) ≃ JoinData G H T U where
  toFun := decomposeJoin
  invFun := JoinData.matching
  left_inv := matching_decomposeJoin
  right_inv := decomposeJoin_matching

noncomputable instance [Fintype V] [Fintype W] : Fintype (JoinData G H T U) :=
  Fintype.ofEquiv (EncodedMatching (joinGraph G H T U)) joinMatchingEquiv

end HiddenCircuits.DH
