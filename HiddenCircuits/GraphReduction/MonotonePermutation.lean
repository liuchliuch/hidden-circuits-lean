import HiddenCircuits.GraphReduction.PermutationMonotone
import HiddenCircuits.CutMatching

/-! The reverse half of the finite monotone/bipartite-permutation equivalence.
The endpoint construction uses slots between columns and retains empty intervals,
isolated labels, and empty parts without a separate deletion convention. -/
namespace HiddenCircuits.GraphReduction

namespace MonotoneOrdering

private def rowSlot (m b : ℕ) (i : Fin m) : ℕ := b*(m+1)+i.val
private def columnSlot (m j : ℕ) : ℕ := j*(m+1)+m

private lemma rowSlot_lt_columnSlot (m b j : ℕ) (i : Fin m) :
    rowSlot m b i < columnSlot m j ↔ b ≤ j := by
  unfold rowSlot columnSlot
  constructor
  · intro h
    by_contra hn
    have hh := Nat.mul_le_mul_right (m+1) (show j+1≤b by omega)
    nlinarith [i.isLt]
  · intro h
    have hh := Nat.mul_le_mul_right (m+1) h
    omega

private lemma columnSlot_lt_rowSlot (m b j : ℕ) (i : Fin m) :
    columnSlot m j < rowSlot m b i ↔ j < b := by
  unfold rowSlot columnSlot
  constructor
  · intro h
    by_contra hn
    have hh := Nat.mul_le_mul_right (m+1) (show b≤j by omega)
    omega
  · intro h
    have hh := Nat.mul_le_mul_right (m+1) (show j+1≤b by omega)
    nlinarith

private lemma rowSlot_ne_columnSlot (m b j : ℕ) (i : Fin m) :
    rowSlot m b i ≠ columnSlot m j := by
  rcases le_or_gt b j with h | h
  · exact (rowSlot_lt_columnSlot m b j i |>.mpr h).ne
  · exact (columnSlot_lt_rowSlot m b j i |>.mpr h).ne.symm

private lemma rowSlot_strictMono {m : ℕ} {f : Fin m → ℕ} (hf : Monotone f) :
    StrictMono (fun i => rowSlot m (f i) i) := by
  intro i j hij
  have hh := Nat.mul_le_mul_right (m+1) (hf hij.le)
  unfold rowSlot
  exact Nat.add_lt_add_of_le_of_lt hh hij

private lemma columnSlot_strictMono (m : ℕ) : StrictMono (columnSlot m) := by
  intro i j hij
  unfold columnSlot
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hij (by omega)) m

private def slotRank {m n : ℕ} (f : Fin m → ℕ) : Fin m ⊕ Fin n → ℕ
  | .inl i => rowSlot m (f i) i
  | .inr j => columnSlot m j.val

private lemma slotRank_injective {m n : ℕ} {f : Fin m → ℕ} (hf : Monotone f) :
    Function.Injective (slotRank (n := n) f) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl ((rowSlot_strictMono hf).injective hab)
    | inr j => exact (rowSlot_ne_columnSlot m (f i) j.val i hab).elim
  | inr i =>
    cases b with
    | inl j => exact (rowSlot_ne_columnSlot m (f j) i.val j hab.symm).elim
    | inr j => exact congrArg Sum.inr (Fin.ext ((columnSlot_strictMono m).injective hab))

variable {X Y : Type*} [Fintype X] [Fintype Y] {R : X → Y → Prop}

/-- Upper row endpoints occupy the `lo` slots; lower row endpoints occupy `hi` slots.
Columns have identical positions on both lines. -/
def indexedDiagram (o : MonotoneOrdering R) :
    PermutationDiagram (Fin (Fintype.card X) ⊕ Fin (Fintype.card Y)) where
  upper := ⟨slotRank o.lo,slotRank_injective o.lo_mono⟩
  lower := ⟨slotRank o.hi,slotRank_injective o.hi_mono⟩

private lemma indexedDiagram_rows (o : MonotoneOrdering R) (i k : Fin (Fintype.card X)) :
    ¬o.indexedDiagram.graph.Adj (.inl i) (.inl k) := by
  have hu := rowSlot_strictMono o.lo_mono
  have hl := rowSlot_strictMono o.hi_mono
  change ¬ ((rowSlot _ (o.lo i) i < rowSlot _ (o.lo k) k ∧
    rowSlot _ (o.hi k) k < rowSlot _ (o.hi i) i) ∨
    (rowSlot _ (o.lo k) k < rowSlot _ (o.lo i) i ∧
    rowSlot _ (o.hi i) i < rowSlot _ (o.hi k) k))
  rw [hu.lt_iff_lt,hu.lt_iff_lt,hl.lt_iff_lt,hl.lt_iff_lt]
  omega

private lemma indexedDiagram_columns (o : MonotoneOrdering R) (j k : Fin (Fintype.card Y)) :
    ¬o.indexedDiagram.graph.Adj (.inr j) (.inr k) := by
  change ¬ ((columnSlot _ j.val < columnSlot _ k.val ∧ columnSlot _ k.val < columnSlot _ j.val) ∨
    (columnSlot _ k.val < columnSlot _ j.val ∧ columnSlot _ j.val < columnSlot _ k.val))
  omega

lemma indexedDiagram_cross (o : MonotoneOrdering R)
    (i : Fin (Fintype.card X)) (j : Fin (Fintype.card Y)) :
    o.indexedDiagram.graph.Adj (.inl i) (.inr j) ↔ R (o.rows i) (o.columns j) := by
  change ((rowSlot _ (o.lo i) i < columnSlot _ j.val ∧ columnSlot _ j.val < rowSlot _ (o.hi i) i) ∨
    (columnSlot _ j.val < rowSlot _ (o.lo i) i ∧ rowSlot _ (o.hi i) i < columnSlot _ j.val)) ↔ _
  rw [rowSlot_lt_columnSlot,columnSlot_lt_rowSlot,columnSlot_lt_rowSlot,rowSlot_lt_columnSlot,
    o.neighborhood]
  have h := o.lo_le_hi i
  omega

/-- The diagram on the original labeled parts, with no assumption that a vertex is incident. -/
def permutationDiagram (o : MonotoneOrdering R) : PermutationDiagram (X ⊕ Y) where
  upper := (Equiv.sumCongr o.rows.symm o.columns.symm).toEmbedding.trans o.indexedDiagram.upper
  lower := (Equiv.sumCongr o.rows.symm o.columns.symm).toEmbedding.trans o.indexedDiagram.lower

theorem permutationDiagram_graph (o : MonotoneOrdering R) :
    o.permutationDiagram.graph = cutGraph R := by
  ext a b
  cases a with
  | inl x =>
    cases b with
    | inl z => exact iff_false_intro (o.indexedDiagram_rows (o.rows.symm x) (o.rows.symm z))
    | inr y => simpa using o.indexedDiagram_cross (o.rows.symm x) (o.columns.symm y)
  | inr y =>
    cases b with
    | inl x =>
      change o.indexedDiagram.graph.Adj (.inr (o.columns.symm y)) (.inl (o.rows.symm x)) ↔ R x y
      rw [SimpleGraph.adj_comm]
      simpa using o.indexedDiagram_cross (o.rows.symm x) (o.columns.symm y)
    | inr z => exact iff_false_intro (o.indexedDiagram_columns (o.columns.symm y) (o.columns.symm z))

end MonotoneOrdering
end HiddenCircuits.GraphReduction
