import HiddenCircuits.Approximation.CanonicalPaths.MarkedWalks
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-! Construction of a global permutation by replacing a
balanced component. The extension is the actual configuration relative permutation. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
variable {m n : ℕ}

noncomputable def liftPermutation (columns : Fin m ↪ Fin n)
    (baseline : Equiv.Perm (Fin n)) (source configuration : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin n) :=
  (Equiv.Perm.viaEmbedding (configuration.trans source.symm) columns).trans baseline

@[simp] theorem liftPermutation_column (columns : Fin m ↪ Fin n)
    (rows : Fin m → Fin n) (baseline : Equiv.Perm (Fin n))
    (source configuration : Equiv.Perm (Fin m))
    (hbase : ∀i,baseline (columns i)=rows (source i)) (i : Fin m) :
    liftPermutation columns baseline source configuration (columns i)=rows (configuration i) := by
  simp only [liftPermutation,Equiv.trans_apply,Equiv.Perm.viaEmbedding_apply,hbase,
    Equiv.apply_symm_apply]

theorem liftPermutation_outside (columns : Fin m ↪ Fin n)
    (baseline : Equiv.Perm (Fin n)) (source configuration : Equiv.Perm (Fin m))
    (i : Fin n) (hi : i∉Set.range columns) :
    liftPermutation columns baseline source configuration i=baseline i := by
  simp only [liftPermutation,Equiv.trans_apply,Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hi]

@[simp] theorem liftPermutation_source (columns : Fin m ↪ Fin n)
    (baseline : Equiv.Perm (Fin n)) (source : Equiv.Perm (Fin m)) :
    liftPermutation columns baseline source source=baseline := by
  apply Equiv.ext
  intro i
  by_cases hi : i∈Set.range columns
  · obtain ⟨j,rfl⟩ := hi
    simp [liftPermutation,Equiv.Perm.viaEmbedding_apply]
  · exact liftPermutation_outside columns baseline source source i hi

theorem liftPermutation_swap (columns : Fin m ↪ Fin n)
    (baseline : Equiv.Perm (Fin n)) (source configuration : Equiv.Perm (Fin m)) (a b : Fin m) :
    liftPermutation columns baseline source ((Equiv.swap a b).trans configuration)=
      (Equiv.swap (columns a) (columns b)).trans (liftPermutation columns baseline source configuration) := by
  apply Equiv.ext
  intro i
  by_cases hi : i∈Set.range columns
  · obtain ⟨j,rfl⟩ := hi
    have hs : Equiv.swap (columns a) (columns b) (columns j)=columns (Equiv.swap a b j) := by
      by_cases hja : j=a
      · subst j; simp
      by_cases hjb : j=b
      · subst j; simp
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb,
          Equiv.swap_apply_of_ne_of_ne (fun h => hja (columns.injective h))
            (fun h => hjb (columns.injective h))]
    simp only [Equiv.trans_apply,hs,liftPermutation,Equiv.Perm.viaEmbedding_apply]
  · have hia : i≠columns a := fun h => hi ⟨a,h.symm⟩
    have hib : i≠columns b := fun h => hi ⟨b,h.symm⟩
    simp only [Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hia hib,
      liftPermutation_outside _ _ _ _ i hi]

noncomputable def liftState {R : Fin n → Fin n → Prop} {r : Fin m → Fin m → Prop}
    (columns : Fin m ↪ Fin n) (rows : Fin m → Fin n)
    (baseline : State R) (source : Equiv.Perm (Fin m))
    (hbase : ∀i,baseline.val (columns i)=rows (source i))
    (hvalid : ∀i j,r i j → R (columns i) (rows j)) (configuration : State r) : State R := by
  refine ⟨liftPermutation columns baseline.val source configuration.val,?_⟩
  intro i
  by_cases hi : i∈Set.range columns
  · obtain ⟨j,rfl⟩ := hi
    rw [liftPermutation_column columns rows baseline.val source configuration.val hbase]
    exact hvalid j (configuration.val j) (configuration.property j)
  · rw [liftPermutation_outside columns baseline.val source configuration.val i hi]
    exact baseline.property i

@[simp] theorem liftState_column {R : Fin n → Fin n → Prop} {r : Fin m → Fin m → Prop}
    (columns : Fin m ↪ Fin n) (rows : Fin m → Fin n)
    (baseline : State R) (source : Equiv.Perm (Fin m))
    (hbase : ∀i,baseline.val (columns i)=rows (source i))
    (hvalid : ∀i j,r i j → R (columns i) (rows j)) (configuration : State r) (i : Fin m) :
    (liftState columns rows baseline source hbase hvalid configuration).val (columns i)=rows (configuration.val i) :=
  liftPermutation_column columns rows baseline.val source configuration.val hbase i

theorem liftState_outside {R : Fin n → Fin n → Prop} {r : Fin m → Fin m → Prop}
    (columns : Fin m ↪ Fin n) (rows : Fin m → Fin n)
    (baseline : State R) (source : Equiv.Perm (Fin m))
    (hbase : ∀i,baseline.val (columns i)=rows (source i))
    (hvalid : ∀i j,r i j → R (columns i) (rows j)) (configuration : State r)
    (i : Fin n) (hi : i∉Set.range columns) :
    (liftState columns rows baseline source hbase hvalid configuration).val i=baseline.val i :=
  liftPermutation_outside columns baseline.val source configuration.val i hi

end HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
