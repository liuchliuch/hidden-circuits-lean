import HiddenCircuits.Approximation.EndpointRestriction
import Mathlib.Order.Fin.Basic

/-! Typed row-zero/column-j deletion for monotone endpoint self-reduction.
The retained vertices keep their original order; the count equality is a
literal restriction/extension bijection, with no graph-code reordering premise. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.EndpointFiber
open GraphReduction Approximation.CanonicalPaths

variable {n : ℕ}

def rowEmbedding : Fin n ↪ Fin (n+1) := ⟨Fin.succ,Fin.succ_injective n⟩
def columnEmbedding (j : Fin (n+1)) : Fin n ↪ Fin (n+1) :=
  ⟨j.succAbove,(Fin.strictMono_succAbove j).injective⟩
lemma row_strict : StrictMono (rowEmbedding (n:=n)) := by
  intro a b h
  change a.val+1<b.val+1
  exact Nat.add_lt_add_right h 1
lemma column_strict (j : Fin (n+1)) : StrictMono (columnEmbedding j) := Fin.strictMono_succAbove j

def deleteFirst (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) : MonotoneEndpoints n :=
  E.restrict rowEmbedding (columnEmbedding j) row_strict (column_strict j)

lemma deleteFirst_allowed (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) (i k : Fin n) :
    ((deleteFirst E j).lo i≤k.val ∧ k.val<(deleteFirst E j).hi i) ↔
      (E.lo i.succ≤(j.succAbove k).val ∧ (j.succAbove k).val<E.hi i.succ) :=
  E.restrict_allowed rowEmbedding (columnEmbedding j) row_strict (column_strict j) i k

abbrev Fiber (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) := {π : E.Permutations // π.val 0=j}

lemma admissible_zero (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) (P : Fiber E j) :
    E.lo 0≤j.val ∧ j.val<E.hi 0 := by
  have h := P.val.property 0
  rw [P.property] at h
  exact h

def restrictPermutation (π : Equiv.Perm (Fin (n+1))) (j : Fin (n+1)) (hπ : π 0=j) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv (0:Fin (n+1))).trans
    ((π.subtypeEquiv (p:=fun x => x≠0) (q:=fun y => y≠j)
      (fun x => by rw [←hπ];exact not_congr π.injective.eq_iff.symm)).trans (finSuccAboveEquiv j).symm)

lemma restrictPermutation_apply (π : Equiv.Perm (Fin (n+1))) (j : Fin (n+1)) (hπ : π 0=j) (i : Fin n) :
    j.succAbove (restrictPermutation π j hπ i)=π i.succ := by
  let e := π.subtypeEquiv (p:=fun x => x≠0) (q:=fun y => y≠j)
    (fun x => by rw [←hπ];exact not_congr π.injective.eq_iff.symm)
  change (finSuccAboveEquiv j ((finSuccAboveEquiv j).symm (e (finSuccAboveEquiv (0:Fin (n+1)) i)))).val=π i.succ
  rw [Equiv.apply_symm_apply]
  rfl

def extendPermutation (j : Fin (n+1)) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' (0:Fin (n+1))).trans (σ.optionCongr.trans (finSuccEquiv' j).symm)

@[simp] lemma extendPermutation_zero (j : Fin (n+1)) (σ : Equiv.Perm (Fin n)) : extendPermutation j σ 0=j := by
  simp [extendPermutation]

@[simp] lemma extendPermutation_succ (j : Fin (n+1)) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPermutation j σ i.succ=j.succAbove (σ i) := by
  change (finSuccEquiv' j).symm (σ.optionCongr (finSuccEquiv' 0 i.succ))=_
  have hi : i.succ=(0:Fin (n+1)).succAbove i := (Fin.zero_succAbove i).symm
  rw [hi,finSuccEquiv'_succAbove]
  simp

lemma restrict_extend (j : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    restrictPermutation (extendPermutation j σ) j (extendPermutation_zero j σ)=σ := by
  apply Equiv.ext
  intro i
  apply (Fin.strictMono_succAbove j).injective
  rw [restrictPermutation_apply,extendPermutation_succ]

lemma extend_restrict (π : Equiv.Perm (Fin (n+1))) (j : Fin (n+1)) (hπ : π 0=j) :
    extendPermutation j (restrictPermutation π j hπ)=π := by
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa using hπ.symm
  · rw [extendPermutation_succ,restrictPermutation_apply]

def restrict (E : MonotoneEndpoints (n+1)) (j : Fin (n+1)) (P : Fiber E j) : (deleteFirst E j).Permutations :=
  ⟨restrictPermutation P.val.val j P.property,fun i => by
    rw [deleteFirst_allowed,restrictPermutation_apply]
    exact P.val.property i.succ⟩

def extend (E : MonotoneEndpoints (n+1)) (j : Fin (n+1))
    (hj : E.lo 0≤j.val ∧ j.val<E.hi 0) (Q : (deleteFirst E j).Permutations) : Fiber E j :=
  ⟨⟨extendPermutation j Q.val,fun i => by
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using hj
    · rw [extendPermutation_succ]
      exact (deleteFirst_allowed E j k (Q.val k)).mp (Q.property k)⟩,extendPermutation_zero j Q.val⟩

/-- Fixing a legal row-zero edge has exactly the residual endpoint matchings as
its completions. The selected column is removed in increasing order. -/
def equivalence (E : MonotoneEndpoints (n+1)) (j : Fin (n+1))
    (hj : E.lo 0≤j.val ∧ j.val<E.hi 0) : Fiber E j ≃ (deleteFirst E j).Permutations where
  toFun := restrict E j
  invFun := extend E j hj
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    exact extend_restrict P.val.val j P.property
  right_inv Q := by
    apply Subtype.ext
    exact restrict_extend j Q.val

theorem card_fiber (E : MonotoneEndpoints (n+1)) (j : Fin (n+1))
    (hj : E.lo 0≤j.val ∧ j.val<E.hi 0) :
    Fintype.card (Fiber E j)=Fintype.card (deleteFirst E j).Permutations :=
  Fintype.card_congr (equivalence E j hj)

theorem card_fiber_zero (E : MonotoneEndpoints (n+1)) (j : Fin (n+1))
    (hj : ¬(E.lo 0≤j.val ∧ j.val<E.hi 0)) : Fintype.card (Fiber E j)=0 := by
  letI : IsEmpty (Fiber E j) := ⟨fun P => hj (admissible_zero E j P)⟩
  exact Fintype.card_eq_zero

/-- Forbidden and padded branch choices must be counted as zero; legal choices
are exactly the ordered endpoint deletions. -/
theorem count_recurrence (E : MonotoneEndpoints (n+1)) :
    Fintype.card E.Permutations=∑j : Fin (n+1),
      if E.lo 0≤j.val ∧ j.val<E.hi 0 then Fintype.card (deleteFirst E j).Permutations else 0 := by
  classical
  calc
    Fintype.card E.Permutations=Fintype.card (Σj : Fin (n+1),Fiber E j) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv (fun π : E.Permutations => π.val 0))).symm
    _=∑j : Fin (n+1),Fintype.card (Fiber E j) := Fintype.card_sigma
    _=_ := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : E.lo 0≤j.val ∧ j.val<E.hi 0
      · rw [if_pos hj,card_fiber E j hj]
      · rw [if_neg hj,card_fiber_zero E j hj]

/-- The terminal empty endpoint instance has one empty permutation. -/
theorem count_empty (E : MonotoneEndpoints 0) : Fintype.card E.Permutations=1 := by
  letI : Unique E.Permutations :=
    { default := ⟨Equiv.refl _,fun i => Fin.elim0 i⟩
      uniq P := by apply Subtype.ext;apply Equiv.ext;intro i;exact Fin.elim0 i }
  exact Fintype.card_unique

end HiddenCircuits.Approximation.SamplerRuntime.EndpointFiber
