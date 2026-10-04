import HiddenCircuits.GraphCounting
import Mathlib.Data.Fintype.Sort

/-! The constructive bipartite permutation-diagram to monotone-ordering implication.
Both interval endpoints are the actual opposite-endpoint counts from Section 2. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators

/-- An actual permutation diagram: every vertex has a distinct rank on each line. -/
structure PermutationDiagram (V : Type*) where
  upper : V ↪ ℕ
  lower : V ↪ ℕ

/-- Two segments cross exactly when their endpoint orders disagree. -/
def PermutationDiagram.Crosses {V : Type*} (D : PermutationDiagram V) (v w : V) : Prop :=
  (D.upper v < D.upper w ∧ D.lower w < D.lower v) ∨
    (D.upper w < D.upper v ∧ D.lower v < D.lower w)

/-- The actual simple graph represented by the two endpoint lists. -/
def PermutationDiagram.graph {V : Type*} (D : PermutationDiagram V) : SimpleGraph V where
  Adj := D.Crosses
  symm := by intro v w; exact Or.symm
  loopless := ⟨by intro v; simp [Crosses]⟩

/-- Sort a finite labeled set by an injective endpoint rank. -/
noncomputable def sortByRank {α : Type*} [Fintype α] (f : α → ℕ) (hf : Function.Injective f) :
    Fin (Fintype.card α) ≃ α := by
  letI := LinearOrder.lift' f hf
  exact (monoEquivOfFin α rfl).toEquiv

 theorem sortByRank_strictMono {α : Type*} [Fintype α] (f : α → ℕ) (hf : Function.Injective f) :
    StrictMono (fun i => f (sortByRank f hf i)) := by
  letI := LinearOrder.lift' f hf
  intro i j hij
  exact (monoEquivOfFin α rfl).strictMono hij

/-- The literal number of opposite-part endpoints strictly preceding a given rank. -/
def endpointCount {α : Type*} [Fintype α] (f : α → ℕ) (t : ℕ) : ℕ :=
  ∑ x, if f x < t then 1 else 0

 theorem endpointCount_card {α : Type*} [Fintype α] (f : α → ℕ) (t : ℕ) :
    endpointCount f t = (Finset.univ.filter (fun x => f x<t)).card := by
  simp only [endpointCount,Finset.sum_boole,Nat.cast_id]

 theorem endpointCount_mono {α : Type*} [Fintype α] (f : α → ℕ) : Monotone (endpointCount f) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> omega

 theorem endpointCount_upper {α : Type*} [Fintype α] (f : α → ℕ) (t : ℕ) :
    endpointCount f t ≤ Fintype.card α := by
  rw [endpointCount_card]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

 theorem endpointCount_comp {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℕ) (t : ℕ) :
    endpointCount (fun x => f (e x)) t = endpointCount f t :=
  Equiv.sum_comp e (fun x => if f x<t then 1 else 0)

/-- In a strictly ordered endpoint list, the count of preceding endpoints is exactly
its initial-segment boundary, including the empty and full segments. -/
theorem endpointCount_index {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f)
    (j : Fin n) (t : ℕ) : f j<t ↔ j.val < endpointCount f t := by
  have hc : endpointCount f t = Fintype.card {a : Fin n // f a<t} := by
    rw [endpointCount_card,Fintype.card_subtype]
  constructor
  · intro hj
    let g : Fin (j.val+1) → {a : Fin n // f a<t} := fun k =>
      ⟨⟨k.val,by have h := j.isLt; omega⟩,
        lt_of_le_of_lt (hf.monotone (by change k.val ≤ j.val; omega)) hj⟩
    have hg : Function.Injective g := by
      intro a b h
      apply Fin.ext
      exact congrArg (fun x : {a : Fin n // f a<t} => x.val.val) h
    have hb := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin,← hc] at hb
    omega
  · intro hj
    by_contra hn
    let g : {a : Fin n // f a<t} → Fin j.val := fun a =>
      ⟨a.val.val,by
        by_contra ha
        have hh := hf.monotone (show j≤a.val by change j.val≤a.val.val; omega)
        have hp := a.property
        omega⟩
    have hg : Function.Injective g := by
      intro a b h
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun z : Fin j.val => z.val) h
    have hb := Fintype.card_le_of_injective g hg
    rw [Fintype.card_fin,← hc] at hb
    omega

/-- A concrete row/column ordering with nondecreasing half-open neighborhood intervals.
The interval `[lo,hi)` is the paper's one-based interval `[lo+1,hi]`. -/
structure MonotoneOrdering {X Y : Type*} [Fintype X] [Fintype Y] (R : X → Y → Prop) where
  rows : Fin (Fintype.card X) ≃ X
  columns : Fin (Fintype.card Y) ≃ Y
  lo : Fin (Fintype.card X) → ℕ
  hi : Fin (Fintype.card X) → ℕ
  lo_mono : Monotone lo
  hi_mono : Monotone hi
  lo_le_hi : ∀ i, lo i ≤ hi i
  hi_le : ∀ i, hi i ≤ Fintype.card Y
  neighborhood : ∀ i j, R (rows i) (columns j) ↔ lo i ≤ j.val ∧ j.val < hi i

namespace PermutationDiagram
variable {X Y : Type*} (D : PermutationDiagram (X ⊕ Y))

/-- Independence forces a part to have the same relative order on the two lines. -/
theorem lower_lt_of_upper_lt (v w : X ⊕ Y) (hn : ¬D.graph.Adj v w)
    (hu : D.upper v < D.upper w) : D.lower v < D.lower w := by
  have hne : D.lower v ≠ D.lower w := by
    intro he
    have hvw := D.lower.injective he
    rw [hvw] at hu
    omega
  by_contra hb
  apply hn
  exact Or.inl ⟨hu,by omega⟩

variable [Fintype X] [Fintype Y]

noncomputable def rowOrder : Fin (Fintype.card X) ≃ X :=
  sortByRank (fun x => D.upper (.inl x)) (D.upper.injective.comp Sum.inl_injective)
noncomputable def columnOrder : Fin (Fintype.card Y) ≃ Y :=
  sortByRank (fun y => D.upper (.inr y)) (D.upper.injective.comp Sum.inr_injective)

/-- Opposite upper endpoints preceding a row's upper endpoint. -/
noncomputable def upperBefore (i : Fin (Fintype.card X)) : ℕ :=
  endpointCount (fun y => D.upper (.inr y)) (D.upper (.inl (D.rowOrder i)))
/-- Opposite lower endpoints preceding the same row's lower endpoint. -/
noncomputable def lowerBefore (i : Fin (Fintype.card X)) : ℕ :=
  endpointCount (fun y => D.lower (.inr y)) (D.lower (.inl (D.rowOrder i)))

 theorem upper_rows_strict : StrictMono (fun i => D.upper (.inl (D.rowOrder i))) :=
  sortByRank_strictMono (fun x => D.upper (.inl x)) (D.upper.injective.comp Sum.inl_injective)
 theorem upper_columns_strict : StrictMono (fun i => D.upper (.inr (D.columnOrder i))) :=
  sortByRank_strictMono (fun y => D.upper (.inr y)) (D.upper.injective.comp Sum.inr_injective)

 theorem lower_rows_strict (hX : ∀ x x', ¬D.graph.Adj (.inl x) (.inl x')) :
    StrictMono (fun i => D.lower (.inl (D.rowOrder i))) := by
  intro i j hij
  exact D.lower_lt_of_upper_lt _ _ (hX _ _) (D.upper_rows_strict hij)
 theorem lower_columns_strict (hY : ∀ y y', ¬D.graph.Adj (.inr y) (.inr y')) :
    StrictMono (fun i => D.lower (.inr (D.columnOrder i))) := by
  intro i j hij
  exact D.lower_lt_of_upper_lt _ _ (hY _ _) (D.upper_columns_strict hij)

 theorem upperBefore_mono : Monotone D.upperBefore :=
  (endpointCount_mono _).comp D.upper_rows_strict.monotone
 theorem lowerBefore_mono (hX : ∀ x x', ¬D.graph.Adj (.inl x) (.inl x')) :
    Monotone D.lowerBefore :=
  (endpointCount_mono _).comp (D.lower_rows_strict hX).monotone

/-- The precise min/max endpoint-count formula, proved from actual crossing orders. -/
theorem neighborhood_counts (hY : ∀ y y', ¬D.graph.Adj (.inr y) (.inr y'))
    (i : Fin (Fintype.card X)) (j : Fin (Fintype.card Y)) :
    D.graph.Adj (.inl (D.rowOrder i)) (.inr (D.columnOrder j)) ↔
      min (D.upperBefore i) (D.lowerBefore i) ≤ j.val ∧
        j.val < max (D.upperBefore i) (D.lowerBefore i) := by
  have hu := endpointCount_index (fun j => D.upper (.inr (D.columnOrder j)))
    D.upper_columns_strict j (D.upper (.inl (D.rowOrder i)))
  have hb := endpointCount_index (fun j => D.lower (.inr (D.columnOrder j)))
    (D.lower_columns_strict hY) j (D.lower (.inl (D.rowOrder i)))
  rw [endpointCount_comp D.columnOrder (fun y => D.upper (.inr y)) _] at hu
  rw [endpointCount_comp D.columnOrder (fun y => D.lower (.inr y)) _] at hb
  have hnu : D.upper (.inl (D.rowOrder i)) ≠ D.upper (.inr (D.columnOrder j)) := by
    intro he
    exact Sum.inl_ne_inr (D.upper.injective he)
  have hnb : D.lower (.inl (D.rowOrder i)) ≠ D.lower (.inr (D.columnOrder j)) := by
    intro he
    exact Sum.inl_ne_inr (D.lower.injective he)
  change (D.upper (.inl (D.rowOrder i)) < D.upper (.inr (D.columnOrder j)) ∧
      D.lower (.inr (D.columnOrder j)) < D.lower (.inl (D.rowOrder i))) ∨
    (D.upper (.inr (D.columnOrder j)) < D.upper (.inl (D.rowOrder i)) ∧
      D.lower (.inl (D.rowOrder i)) < D.lower (.inr (D.columnOrder j))) ↔ _
  change _ ↔ j.val < D.upperBefore i at hu
  change _ ↔ j.val < D.lowerBefore i at hb
  omega

/-- Every actual finite bipartite permutation diagram yields an explicit monotone
ordering. Isolated rows give the allowed empty intervals without any exception. -/
noncomputable def monotoneOrdering
    (hX : ∀ x x', ¬D.graph.Adj (.inl x) (.inl x'))
    (hY : ∀ y y', ¬D.graph.Adj (.inr y) (.inr y')) :
    MonotoneOrdering (fun x y => D.graph.Adj (.inl x) (.inr y)) where
  rows := D.rowOrder
  columns := D.columnOrder
  lo i := min (D.upperBefore i) (D.lowerBefore i)
  hi i := max (D.upperBefore i) (D.lowerBefore i)
  lo_mono _i _j h := min_le_min (D.upperBefore_mono h) (D.lowerBefore_mono hX h)
  hi_mono _i _j h := max_le_max (D.upperBefore_mono h) (D.lowerBefore_mono hX h)
  lo_le_hi _i := (min_le_left _ _).trans (le_max_left _ _)
  hi_le _i := max_le (endpointCount_upper _ _) (endpointCount_upper _ _)
  neighborhood := D.neighborhood_counts hY

end PermutationDiagram
end HiddenCircuits.GraphReduction
