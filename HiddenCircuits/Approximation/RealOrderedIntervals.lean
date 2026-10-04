import HiddenCircuits.Approximation.OrderedIntervals
import HiddenCircuits.GraphReduction.RealUnitIntervals

/-!
# Monotone orderings of finite real equal-length interval cuts

The tie-breaker orders vertex identities only after comparing real endpoints.
Repeated endpoints remain repeated labeled vertices. No rationalization,
recognition algorithm, or represented input assumption is used.
-/
namespace HiddenCircuits.Approximation
open HiddenCircuits.GraphReduction
attribute [local instance] Classical.propDecidable

namespace RealOrderedIntervals

private noncomputable def coordinateKey {α : Type*} [Fintype α] (f : α → ℝ)
    (x : α) : ℝ ×ₗ Fin (Fintype.card α) := toLex (f x, Fintype.equivFin α x)

private theorem coordinateKey_injective {α : Type*} [Fintype α] (f : α → ℝ) :
    Function.Injective (coordinateKey f) := by
  intro x y h
  exact (Fintype.equivFin α).injective
    (congrArg (fun z : ℝ ×ₗ Fin (Fintype.card α) => (ofLex z).2) h)

/-- Sort real coordinates, breaking ties only to obtain a bijection. -/
noncomputable def coordinateOrder {α : Type*} [Fintype α] (f : α → ℝ) :
    Fin (Fintype.card α) ≃ α := by
  letI := LinearOrder.lift' (coordinateKey f) (coordinateKey_injective f)
  exact (monoEquivOfFin α rfl).toEquiv

theorem coordinateOrder_mono {α : Type*} [Fintype α] (f : α → ℝ) :
    Monotone (fun i => f (coordinateOrder f i)) := by
  letI := LinearOrder.lift' (coordinateKey f) (coordinateKey_injective f)
  intro i j hij
  have h := (monoEquivOfFin α rfl).monotone hij
  change coordinateKey f (coordinateOrder f i) ≤ coordinateKey f (coordinateOrder f j) at h
  rcases Prod.Lex.le_iff.mp h with h|h
  · exact h.le
  · exact h.1.le

/-- Count the entries strictly before a real threshold. -/
noncomputable def before {α : Type*} [Fintype α] (f : α → ℝ) (t : ℝ) : ℕ :=
  Fintype.card {x : α // f x < t}

/-- Count the entries at or before a real threshold. -/
noncomputable def through {α : Type*} [Fintype α] (f : α → ℝ) (t : ℝ) : ℕ :=
  Fintype.card {x : α // f x ≤ t}

theorem before_index {n : ℕ} (f : Fin n → ℝ) (hf : Monotone f)
    (j : Fin n) (t : ℝ) : f j<t ↔ j.val < before f t :=
  prefix_iff_card (fun i => f i<t) (fun _ _ hik hk => (hf hik).trans_lt hk) j

theorem through_index {n : ℕ} (f : Fin n → ℝ) (hf : Monotone f)
    (j : Fin n) (t : ℝ) : f j≤t ↔ j.val < through f t :=
  prefix_iff_card (fun i => f i≤t) (fun _ _ hik hk => (hf hik).trans hk) j

private theorem card_subtype_mono {α : Type*} [Fintype α] {P Q : α → Prop}
    (h : ∀ a, P a → Q a) : Fintype.card {a // P a} ≤ Fintype.card {a // Q a} := by
  classical
  exact Fintype.card_le_of_injective
    (fun a : {a // P a} => (⟨a.val,h a.val a.property⟩ : {a // Q a}))
    (fun _ _ hh => Subtype.ext (congrArg (fun a : {a // Q a} => a.val) hh))

theorem before_mono {α : Type*} [Fintype α] (f : α → ℝ) : Monotone (before f) := by
  intro s t hst
  unfold before
  simpa only [Fintype.card_eq_nat_card] using
    (card_subtype_mono (P := fun x => f x<s) (Q := fun x => f x<t) (fun _ h => h.trans_le hst))

theorem through_mono {α : Type*} [Fintype α] (f : α → ℝ) : Monotone (through f) := by
  intro s t hst
  unfold through
  simpa only [Fintype.card_eq_nat_card] using
    (card_subtype_mono (P := fun x => f x≤s) (Q := fun x => f x≤t) (fun _ h => h.trans hst))

/-- Equal-length interval intersection gives literal monotone row boundaries. -/
noncomputable def intervalOverlapOrdering {X Y : Type*} [Fintype X] [Fintype Y]
    (a : X → ℝ) (b : Y → ℝ) (L : ℝ) (hL : 0≤L) :
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

end RealOrderedIntervals

/-- Every finite graph represented by closed real intervals of common positive
length is quasimonotone, including coincident and touching intervals. -/
theorem RealUnitInterval.Representation.quasimonotone {V : Type*} [Fintype V]
    {G : SimpleGraph V} (r : GraphReduction.RealUnitInterval.Representation G) :
    Quasimonotone G := by
  classical
  intro S
  let o := RealOrderedIntervals.intervalOverlapOrdering (fun x : S => r.left x.val)
    (fun y : {v // v ∉ S} => r.left y.val) r.length r.positive.le
  refine ⟨{ o with neighborhood := ?_ }⟩
  intro i j
  rw [r.adjacency]
  have hne : (o.rows i).val ≠ (o.columns j).val := by
    intro h
    exact (o.columns j).property (h ▸ (o.rows i).property)
  rw [and_iff_right hne, GraphReduction.RealUnitInterval.icc_overlap
    (by linarith [r.positive]) (by linarith [r.positive])]
  exact o.neighborhood i j

/-- Class-level inclusion needs only the semantic graph promise. -/
theorem realUnitIntervalGraph_quasimonotone {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : GraphReduction.RealUnitInterval.UnitIntervalGraph G) :
    Quasimonotone G :=
  RealUnitInterval.Representation.quasimonotone hG.some

end HiddenCircuits.Approximation
