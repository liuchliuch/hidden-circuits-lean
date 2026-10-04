import HiddenCircuits.GraphReduction.PermutationMonotone
import HiddenCircuits.GraphReduction.UnitIntervalProbeRepresentation
import Mathlib.Data.Prod.Lex

/-!
# Ordered interval foundations for self-reduction

This file proves the geometric inclusion in Corollaries 1.3–1.4 directly.
Coincident endpoints are allowed. No graph-recognition or mixing oracle occurs.
-/
namespace HiddenCircuits.Approximation
open HiddenCircuits.GraphReduction
attribute [local instance] Classical.propDecidable

private noncomputable def coordinateKey {α : Type*} [Fintype α] (f : α → ℚ)
    (x : α) : ℚ ×ₗ Fin (Fintype.card α) := toLex (f x, Fintype.equivFin α x)

private theorem coordinateKey_injective {α : Type*} [Fintype α] (f : α → ℚ) :
    Function.Injective (coordinateKey f) := by
  intro x y h
  exact (Fintype.equivFin α).injective
    (congrArg (fun z : ℚ ×ₗ Fin (Fintype.card α) => (ofLex z).2) h)

/-- Sort rational coordinates, breaking ties only to obtain a bijection. -/
noncomputable def coordinateOrder {α : Type*} [Fintype α] (f : α → ℚ) :
    Fin (Fintype.card α) ≃ α := by
  letI := LinearOrder.lift' (coordinateKey f) (coordinateKey_injective f)
  exact (monoEquivOfFin α rfl).toEquiv

theorem coordinateOrder_mono {α : Type*} [Fintype α] (f : α → ℚ) :
    Monotone (fun i => f (coordinateOrder f i)) := by
  letI := LinearOrder.lift' (coordinateKey f) (coordinateKey_injective f)
  intro i j hij
  have h := (monoEquivOfFin α rfl).monotone hij
  change coordinateKey f (coordinateOrder f i) ≤ coordinateKey f (coordinateOrder f j) at h
  rcases Prod.Lex.le_iff.mp h with h|h
  · exact h.le
  · exact h.1.le

/-- A downward closed predicate on a finite linear list is its initial segment. -/
theorem prefix_iff_card {n : ℕ} (P : Fin n → Prop)
    (hP : ∀ i j, i≤j → P j → P i) (j : Fin n) :
    P j ↔ j.val < Fintype.card {i : Fin n // P i} := by
  classical
  constructor
  · intro hj
    let g : Fin (j.val+1) → {i : Fin n // P i} := fun k =>
      ⟨⟨k.val,by omega⟩,hP _ j (by change k.val≤j.val; omega) hj⟩
    have hg : Function.Injective g := by
      intro a b h
      exact Fin.ext (congrArg (fun z : {i : Fin n // P i} => z.val.val) h)
    have h := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin] at h
    omega
  · intro hj
    by_contra hn
    let g : {i : Fin n // P i} → Fin j.val := fun i =>
      ⟨i.val.val,by
        by_contra h
        exact hn (hP j i.val (by change j.val ≤ i.val.val; omega) i.property)⟩
    have hg : Function.Injective g := by
      intro a b h
      exact Subtype.ext (Fin.ext (congrArg (fun z : Fin j.val => z.val) h))
    have h := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin] at h
    omega

/-- Count the entries strictly before a rational threshold. -/
noncomputable def before {α : Type*} [Fintype α] (f : α → ℚ) (t : ℚ) : ℕ :=
  Fintype.card {x : α // f x < t}

/-- Count the entries at or before a rational threshold. -/
noncomputable def through {α : Type*} [Fintype α] (f : α → ℚ) (t : ℚ) : ℕ :=
  Fintype.card {x : α // f x ≤ t}

private theorem subtype_card_comp {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : β → Prop) :
    Fintype.card {x : α // P (e x)} = Fintype.card {y : β // P y} := by
  classical
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem before_index {n : ℕ} (f : Fin n → ℚ) (hf : Monotone f)
    (j : Fin n) (t : ℚ) : f j<t ↔ j.val < before f t :=
  by
    convert prefix_iff_card (fun i => f i<t) (fun i k hik hk => (hf hik).trans_lt hk) j using 1 <;>
      simp only [before, Fintype.card_eq_nat_card]

theorem through_index {n : ℕ} (f : Fin n → ℚ) (hf : Monotone f)
    (j : Fin n) (t : ℚ) : f j≤t ↔ j.val < through f t :=
  by
    convert prefix_iff_card (fun i => f i≤t) (fun i k hik hk => (hf hik).trans hk) j using 1 <;>
      simp only [through, Fintype.card_eq_nat_card]

private theorem card_subtype_mono {α : Type*} [Fintype α] {P Q : α → Prop}
    (h : ∀ a, P a → Q a) : Fintype.card {a // P a} ≤ Fintype.card {a // Q a} := by
  classical
  exact Fintype.card_le_of_injective
    (fun a : {a // P a} => (⟨a.val,h a.val a.property⟩ : {a // Q a}))
    (fun _ _ hh => Subtype.ext (congrArg (fun a : {a // Q a} => a.val) hh))

theorem before_mono {α : Type*} [Fintype α] (f : α → ℚ) : Monotone (before f) := by
  intro s t hst
  unfold before
  simpa only [Fintype.card_eq_nat_card] using
    (card_subtype_mono (P := fun x => f x<s) (Q := fun x => f x<t) (fun _ h => h.trans_le hst))

theorem through_mono {α : Type*} [Fintype α] (f : α → ℚ) : Monotone (through f) := by
  intro s t hst
  unfold through
  simpa only [Fintype.card_eq_nat_card] using
    (card_subtype_mono (P := fun x => f x≤s) (Q := fun x => f x≤t) (fun _ h => h.trans hst))

/-- Equal-length interval intersection gives literal monotone row boundaries. -/
noncomputable def intervalOverlapOrdering {X Y : Type*} [Fintype X] [Fintype Y]
    (a : X → ℚ) (b : Y → ℚ) (L : ℚ) (hL : 0≤L) :
    MonotoneOrdering (fun x y => a x ≤ b y+L ∧ b y ≤ a x+L) where
  rows := coordinateOrder a
  columns := coordinateOrder b
  lo i := before b (a (coordinateOrder a i)-L)
  hi i := through b (a (coordinateOrder a i)+L)
  lo_mono := (before_mono b).comp (fun _ _ h => sub_le_sub_right (coordinateOrder_mono a h) L)
  hi_mono := (through_mono b).comp (fun _ _ h => by have hh := coordinateOrder_mono a h; linarith)
  lo_le_hi i := by
    unfold before through
    simpa only [Fintype.card_eq_nat_card] using
      (card_subtype_mono (P := fun y => b y<a (coordinateOrder a i)-L)
        (Q := fun y => b y≤a (coordinateOrder a i)+L) (fun y hy => by linarith))
  hi_le i := by
    unfold through
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  neighborhood i j := by
    have hlo := before_index (fun j => b (coordinateOrder b j)) (coordinateOrder_mono b)
      j (a (coordinateOrder a i)-L)
    have hhi := through_index (fun j => b (coordinateOrder b j)) (coordinateOrder_mono b)
      j (a (coordinateOrder a i)+L)
    have hlc : before (fun j => b (coordinateOrder b j)) (a (coordinateOrder a i)-L) =
        before b (a (coordinateOrder a i)-L) := by
      unfold before
      exact Fintype.card_congr ((coordinateOrder b).subtypeEquiv (fun _ => Iff.rfl))
    have hhc : through (fun j => b (coordinateOrder b j)) (a (coordinateOrder a i)+L) =
        through b (a (coordinateOrder a i)+L) := by
      unfold through
      exact Fintype.card_congr ((coordinateOrder b).subtypeEquiv (fun _ => Iff.rfl))
    rw [hlc] at hlo
    rw [hhc] at hhi
    change _ ↔ _≤j.val ∧ j.val<_
    constructor
    · intro h
      refine ⟨?_,hhi.mp h.2⟩
      by_contra hn
      have hb := hlo.mpr (by omega)
      linarith [h.1]
    · intro h
      refine ⟨?_,hhi.mpr h.2⟩
      by_contra hn
      have hb := hlo.mp (by linarith)
      omega

/-- Every vertex cut has an actual monotone ordering of its crossing edges. -/
def Quasimonotone {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop := by
  classical
  exact ∀ S : Set V, Nonempty (MonotoneOrdering (fun x : S => fun y : {v // v ∉ S} => G.Adj x.val y.val))

/-- Direct proof of the unit-interval inclusion, allowing repeated coordinates. -/
theorem UnitInterval.Representation.quasimonotone {V : Type*} [Fintype V]
    {G : SimpleGraph V} (r : UnitInterval.Representation G) : Quasimonotone G := by
  classical
  intro S
  let o := intervalOverlapOrdering (fun x : S => r.left x.val)
    (fun y : {v // v ∉ S} => r.left y.val) r.length r.positive.le
  refine ⟨{ o with neighborhood := ?_ }⟩
  intro i j
  rw [r.adjacency]
  have hne : (o.rows i).val ≠ (o.columns j).val := by
    intro h
    exact (o.columns j).property (h ▸ (o.rows i).property)
  rw [and_iff_right hne, UnitInterval.icc_overlap (by linarith [r.positive]) (by linarith [r.positive])]
  exact o.neighborhood i j

/-- The supplied equal-length representation survives every induced deletion. -/
def UnitInterval.Representation.induce {V : Type*} {G : SimpleGraph V}
    (r : UnitInterval.Representation G) (S : Set V) : UnitInterval.Representation (G.induce S) where
  length := r.length
  positive := r.positive
  left x := r.left x.val
  adjacency x y := by
    change G.Adj x.val y.val ↔ _
    rw [r.adjacency]
    simp only [ne_eq, Subtype.val_inj]

end HiddenCircuits.Approximation
