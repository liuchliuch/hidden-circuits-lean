import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

import Mathlib.Data.Set.Insert
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
variable {α : Type*}
def SameUnion (p q r s : Equiv.Perm α) : Prop := ∀ i, ({p i,q i} : Set α)={r i,s i}
def unionGraph (p q : Equiv.Perm α) : SimpleGraph α where
  Adj i j := i≠j ∧ ∃ x, x∈({p i,q i} : Set α) ∧ x∈({p j,q j} : Set α)
  symm := by rintro i j ⟨h,x,hx,hy⟩; exact ⟨h.symm,x,hy,hx⟩
  loopless := ⟨by rintro i ⟨h,_⟩; exact h rfl⟩
theorem graph_eq_of_sameUnion {p q r s : Equiv.Perm α} (h : SameUnion p q r s) :
    unionGraph p q=unionGraph r s := by
  apply SimpleGraph.ext
  funext i j
  apply propext
  change (i≠j ∧ ∃ x, x∈({p i,q i} : Set α) ∧ x∈({p j,q j} : Set α)) ↔ _
  rw [h i,h j]
  rfl
private theorem pair_right_cancel {a b c : α} (h : ({a,b} : Set α)={a,c}) : b=c := by
  rcases Set.pair_eq_pair_iff.mp h with h|h
  · exact h.2
  · exact h.2.trans h.1
theorem right_eq_of_left_eq {p q r s : Equiv.Perm α} (h : SameUnion p q r s)
    {i : α} (hi : r i=p i) : s i=q i := by
  have hh := h i
  rw [hi] at hh
  exact (pair_right_cancel hh).symm
theorem left_eq_of_right_eq {p q r s : Equiv.Perm α} (h : SameUnion p q r s)
    {i : α} (hi : s i=q i) : r i=p i := by
  have hh := h i
  rw [hi] at hh
  have hc : ({q i,p i} : Set α)={q i,r i} := by simpa only [Set.pair_comm] using hh
  exact (pair_right_cancel hc).symm
theorem crossing_of_adj {p q : Equiv.Perm α} {i j : α} (h : (unionGraph p q).Adj i j) :
    p i=q j ∨ q i=p j := by
  rcases h with ⟨hne,x,hx,hy⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · exact False.elim (hne (p.injective (hx.symm.trans hy)))
  · exact Or.inl (hx.symm.trans hy)
  · exact Or.inr (hx.symm.trans hy)
  · exact False.elim (hne (q.injective (hx.symm.trans hy)))
theorem left_eq_across_edge {p q r s : Equiv.Perm α} (h : SameUnion p q r s)
    {i j : α} (hij : (unionGraph p q).Adj i j) (hi : r i=p i) : r j=p j := by
  have hsi := right_eq_of_left_eq h hi
  have hrj : r j=p j ∨ r j=q j := by
    have hh : r j∈({p j,q j} : Set α) := by rw [h j]; simp
    simpa using hh
  have hsj : s j=p j ∨ s j=q j := by
    have hh : s j∈({p j,q j} : Set α) := by rw [h j]; simp
    simpa using hh
  rcases crossing_of_adj hij with he|he
  · rcases hrj with hj|hj
    · exact hj
    · exact False.elim (hij.1 ((r.injective (hi.trans (he.trans hj.symm)))))
  · rcases hsj with hj|hj
    · exact False.elim (hij.1 (s.injective (hsi.trans (he.trans hj.symm))))
    · exact left_eq_of_right_eq h hj
theorem left_eq_of_reachable {p q r s : Equiv.Perm α} (h : SameUnion p q r s)
    {i j : α} (hij : (unionGraph p q).Reachable i j) (hi : r i=p i) : r j=p j := by
  have aux : ∀ {u v}, (unionGraph p q).Walk u v → r u=p u → r v=p v := by
    intro u v w
    induction w with
    | nil => exact id
    | cons huv path ih =>
      intro hleft
      exact ih (left_eq_across_edge h huv hleft)
  exact hij.elim (fun w => aux w hi)
theorem determined_by_representatives {p q r s : Equiv.Perm α} (h : SameUnion p q r s)
    (hreps : ∀ j, ∃ i, (unionGraph p q).Reachable i j ∧ r i=p i) : p=r ∧ q=s := by
  have hp : ∀ j, r j=p j := by
    intro j
    obtain ⟨i,hij,hi⟩ := hreps j
    exact left_eq_of_reachable h hij hi
  constructor
  · exact (Equiv.ext hp).symm
  · apply Equiv.ext
    intro j
    exact (right_eq_of_left_eq h (hp j)).symm
end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
