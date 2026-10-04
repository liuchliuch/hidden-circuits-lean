import HiddenCircuits.GraphReduction.UnitIntervalProbeRepresentation
import Mathlib.Data.Real.Basic

/-!
# The natural real unit-interval graph class

The graph has ordinary finite labeled vertices. Its class membership means
that closed intervals in the real line, of one common positive length,
represent adjacency. Neither endpoint distinctness nor a coordinate encoding
is imposed. In particular, touching intervals intersect and coincident
intervals represent distinct adjacent vertices.
-/
namespace HiddenCircuits.GraphReduction
namespace RealUnitInterval

/-- Closed real intervals with one common positive length. -/
structure Representation {V : Type*} (G : SimpleGraph V) where
  length : ℝ
  positive : 0 < length
  left : V → ℝ
  adjacency : ∀ x y, G.Adj x y ↔ x ≠ y ∧
    (Set.Icc (left x) (left x + length) ∩
      Set.Icc (left y) (left y + length)).Nonempty

/-- The ordinary graph-class predicate; coordinates are existential witnesses,
not additional input to any graph algorithm or counting oracle. -/
def UnitIntervalGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (Representation G)

/-- Endpoint inequalities characterize overlap of closed real intervals. -/
theorem icc_overlap {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (Set.Icc a b ∩ Set.Icc c d).Nonempty ↔ a ≤ d ∧ c ≤ b := by
  constructor
  · rintro ⟨x, ⟨hax, hxb⟩, ⟨hcx, hxd⟩⟩
    exact ⟨hax.trans hxd, hcx.trans hxb⟩
  · rintro ⟨had, hcb⟩
    exact ⟨max a c, ⟨le_max_left _ _, max_le hab hcb⟩,
      ⟨le_max_right _ _, max_le had hcd⟩⟩

/-- A real representation restricts to every induced graph. -/
def Representation.induce {V : Type*} {G : SimpleGraph V}
    (r : Representation G) (S : Set V) : Representation (G.induce S) where
  length := r.length
  positive := r.positive
  left x := r.left x.val
  adjacency x y := by
    change G.Adj x.val y.val ↔ _
    rw [r.adjacency]
    simp only [ne_eq, Subtype.val_inj]

/-- Scaling by the positive common length gives intervals of length one. -/
noncomputable def Representation.unitLength {V : Type*} {G : SimpleGraph V}
    (r : Representation G) : Representation G where
  length := 1
  positive := by norm_num
  left v := r.left v / r.length
  adjacency := by
    intro x y
    rw [r.adjacency]
    apply and_congr_right
    intro _
    rw [icc_overlap (by linarith [r.positive]) (by linarith [r.positive]),
      icc_overlap (by linarith) (by linarith)]
    have hx : r.left x / r.length + 1 = (r.left x + r.length) / r.length := by
      rw [add_div, div_self (ne_of_gt r.positive)]
    have hy : r.left y / r.length + 1 = (r.left y + r.length) / r.length := by
      rw [add_div, div_self (ne_of_gt r.positive)]
    rw [hx, hy, div_le_div_iff_of_pos_right r.positive,
      div_le_div_iff_of_pos_right r.positive]

@[simp] theorem Representation.unitLength_length {V : Type*} {G : SimpleGraph V}
    (r : Representation G) : r.unitLength.length = 1 := rfl

end RealUnitInterval

/-- The concrete rational representations used by the reduction are genuine
closed-real-interval representations of exactly the same labeled graph. -/
noncomputable def UnitInterval.Representation.toReal {V : Type*} {G : SimpleGraph V}
    (r : UnitInterval.Representation G) : RealUnitInterval.Representation G where
  length := (r.length : ℝ)
  positive := by exact_mod_cast r.positive
  left v := (r.left v : ℝ)
  adjacency := by
    intro x y
    rw [r.adjacency]
    apply and_congr_right
    intro _
    rw [UnitInterval.icc_overlap (by linarith [r.positive]) (by linarith [r.positive]),
      RealUnitInterval.icc_overlap (by exact_mod_cast (show r.left x ≤ r.left x + r.length by linarith [r.positive]))
        (by exact_mod_cast (show r.left y ≤ r.left y + r.length by linarith [r.positive]))]
    norm_cast

@[simp] theorem UnitInterval.Representation.toReal_length {V : Type*} {G : SimpleGraph V}
    (r : UnitInterval.Representation G) : r.toReal.length = (r.length : ℝ) := rfl

@[simp] theorem UnitInterval.Representation.toReal_left {V : Type*} {G : SimpleGraph V}
    (r : UnitInterval.Representation G) (v : V) : r.toReal.left v = (r.left v : ℝ) := rfl

end HiddenCircuits.GraphReduction
