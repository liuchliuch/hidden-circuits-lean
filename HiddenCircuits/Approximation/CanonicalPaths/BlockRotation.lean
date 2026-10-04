import HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
import Mathlib.GroupTheory.Perm.Fin

/-! Fresh explicit one-dislocation permutations for cycle token configurations. -/
namespace HiddenCircuits.Approximation.CanonicalPaths
variable {n : ℕ}

def blockRotation (a b : Fin n) : Equiv.Perm (Fin n) :=
  (Fin.cycleIcc a b).symm.trans (finRotate n)

theorem rotate_apply [NeZero n] (i : Fin n) : finRotate n i=i+1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact finRotate_succ_apply i

theorem blockRotation_start [NeZero n] (a b : Fin n) (hab : a ≤ b) :
    blockRotation a b a=finRotate n b := by
  change finRotate n ((Fin.cycleIcc a b).symm a)=finRotate n b
  have hp : (Fin.cycleIcc a b).symm a=b := (Fin.cycleIcc a b).symm_apply_eq.mpr (Fin.cycleIcc_of_last hab).symm
  rw [hp]

theorem blockRotation_inside [NeZero n] (a b i : Fin n) (hai : a < i) (hib : i ≤ b) :
    blockRotation a b i=i := by
  have hi₀ : i≠0 := by intro h; subst i; exact not_lt_of_ge (Fin.zero_le a) hai
  let j := (finRotate n).symm i
  have hj : j.val=i.val-1 := coe_finRotate_symm_of_ne_zero hi₀
  have haj : a ≤ j := by change a.val ≤ j.val; rw [hj]; change a.val < i.val at hai; omega
  have hjb : j < b := by change j.val < b.val; rw [hj]; change i.val ≤ b.val at hib; change a.val < i.val at hai; omega
  have he : Fin.cycleIcc a b j=i := by
    rw [Fin.cycleIcc_of_ge_of_lt haj hjb,← rotate_apply]
    exact (finRotate n).apply_symm_apply i
  change finRotate n ((Fin.cycleIcc a b).symm i)=i
  have hp : (Fin.cycleIcc a b).symm i=j := (Fin.cycleIcc a b).symm_apply_eq.mpr he.symm
  rw [hp]
  exact (finRotate n).apply_symm_apply i

theorem blockRotation_outside [NeZero n] (a b i : Fin n) (hi : i < a ∨ b < i) :
    blockRotation a b i=finRotate n i := by
  have he : Fin.cycleIcc a b i=i := hi.elim Fin.cycleIcc_of_lt Fin.cycleIcc_of_gt
  change finRotate n ((Fin.cycleIcc a b).symm i)=finRotate n i
  have hp : (Fin.cycleIcc a b).symm i=i := (Fin.cycleIcc a b).symm_apply_eq.mpr he.symm
  rw [hp]

theorem blockRotation_apply [NeZero n] (a b i : Fin n) (hab : a ≤ b) :
    blockRotation a b i=if i=a then finRotate n b else if a < i ∧ i ≤ b then i else finRotate n i := by
  by_cases hi : i=a
  · subst i
    simpa only [if_pos rfl] using blockRotation_start a b hab
  by_cases hin : a < i ∧ i ≤ b
  · simpa only [if_neg hi,if_pos hin] using blockRotation_inside a b i hin.1 hin.2
  · have hout : i < a ∨ b < i := by
      rcases lt_or_gt_of_ne hi with h|h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge (fun hb => hin ⟨h,hb⟩))
    simpa only [if_neg hi,if_neg hin] using blockRotation_outside a b i hout

theorem cycleIcc_apply [NeZero n] (a b i : Fin n) (hab : a ≤ b) :
    Fin.cycleIcc a b i=if i=b then a else if a ≤ i ∧ i < b then finRotate n i else i := by
  by_cases hi : i=b
  · subst i
    simpa only [if_pos rfl] using Fin.cycleIcc_of_last hab
  by_cases hin : a ≤ i ∧ i < b
  · simpa only [if_neg hi,if_pos hin,rotate_apply] using Fin.cycleIcc_of_ge_of_lt hin.1 hin.2
  · have hout : i < a ∨ b < i := by
      by_cases ha : a ≤ i
      · right
        exact lt_of_le_of_ne (le_of_not_gt (fun hb => hin ⟨ha,hb⟩)) (fun h => hi h.symm)
      · exact Or.inl (lt_of_not_ge ha)
    simp only [if_neg hi,if_neg hin]
    exact hout.elim Fin.cycleIcc_of_lt Fin.cycleIcc_of_gt

theorem blockRotation_admissible [NeZero n] (a b : Fin n) (hab : a ≤ b)
    (R : Fin n → Fin n → Prop) (hp : ∀i,R i i) (hq : ∀i,R i (finRotate n i))
    (hd : R a (finRotate n b)) : ∀i,R i (blockRotation a b i) := by
  intro i
  rw [blockRotation_apply a b i hab]
  split_ifs with hi hin
  · subst i; exact hd
  · exact hp i
  · exact hq i

theorem cycleIcc_admissible [NeZero n] (a b : Fin n) (hab : a ≤ b)
    (R : Fin n → Fin n → Prop) (hp : ∀i,R i i) (hq : ∀i,R i (finRotate n i))
    (hd : R b a) : ∀i,R i (Fin.cycleIcc a b i) := by
  intro i
  rw [cycleIcc_apply a b i hab]
  split_ifs with hi hin
  · subst i; exact hd
  · exact hq i
  · exact hp i

end HiddenCircuits.Approximation.CanonicalPaths
