import HiddenCircuits.Approximation.FiniteCoins
import Mathlib.GroupTheory.Perm.Fin

/-! Sorted endpoint constraints and the diagonal test for admissible permutations. -/
namespace HiddenCircuits.Approximation

structure MonotoneEndpoints (n : ℕ) where
  lo : Fin n → ℕ
  hi : Fin n → ℕ
  lo_mono : Monotone lo
  hi_mono : Monotone hi
  lo_le_hi : ∀ i, lo i ≤ hi i
  hi_le : ∀ i, hi i ≤ n

namespace MonotoneEndpoints
variable {n : ℕ} (E : MonotoneEndpoints n)

def Admissible (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, E.lo i ≤ (π i).val ∧ (π i).val < E.hi i

instance (π : Equiv.Perm (Fin n)) : Decidable (E.Admissible π) :=
  inferInstanceAs (Decidable (∀ i, E.lo i ≤ (π i).val ∧ (π i).val < E.hi i))

abbrev Permutations := {π : Equiv.Perm (Fin n) // E.Admissible π}

/-- An injection cannot send all `i+1` initial labels into the first `i` labels. -/
theorem permutation_prefix_crossing (π : Equiv.Perm (Fin n)) (i : Fin n) :
    ∃ j : Fin n, j ≤ i ∧ i ≤ π j := by
  classical
  by_contra h
  push_neg at h
  let c : Fin (i.val+1) → Fin n := fun j => ⟨j.val,by have := j.isLt; have := i.isLt; omega⟩
  have hc (j : Fin (i.val+1)) : c j ≤ i := by
    change j.val ≤ i.val
    have := j.isLt
    omega
  let f : Fin (i.val+1) → Fin i.val := fun j => ⟨(π (c j)).val,h (c j) (hc j)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hval : (π (c a)).val=(π (c b)).val := congrArg (fun z : Fin i.val => z.val) hab
    have he := π.injective (Fin.ext hval)
    exact congrArg (fun z : Fin n => z.val) he
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

/-- Sorted endpoint constraints admit a permutation only if the diagonal fits. -/
theorem identity_admissible_of_admissible (π : Equiv.Perm (Fin n)) (hπ : E.Admissible π) :
    E.Admissible (Equiv.refl (Fin n)) := by
  intro i
  constructor
  · obtain ⟨j,hji,hij⟩ := permutation_prefix_crossing π.symm i
    have hl := E.lo_mono hij
    have hp := (hπ (π.symm j)).1
    simp only [Equiv.apply_symm_apply] at hp
    exact hl.trans (hp.trans hji)
  · obtain ⟨j,hji,hij⟩ := permutation_prefix_crossing π i
    exact lt_of_le_of_lt hij (lt_of_lt_of_le (hπ j).2 (E.hi_mono hji))

def startingPermutation : Option E.Permutations :=
  if h : E.Admissible (Equiv.refl (Fin n)) then some ⟨Equiv.refl _,h⟩ else none

theorem startingPermutation_none_iff : E.startingPermutation=none ↔ ¬Nonempty E.Permutations := by
  constructor
  · intro h ⟨π⟩
    have hi := E.identity_admissible_of_admissible π.val π.property
    simp [startingPermutation,hi] at h
  · intro h
    have hi : ¬E.Admissible (Equiv.refl (Fin n)) := fun hi => h ⟨⟨Equiv.refl _,hi⟩⟩
    simp [startingPermutation,hi]

end MonotoneEndpoints
end HiddenCircuits.Approximation
