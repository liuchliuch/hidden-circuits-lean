import HiddenCircuits.Approximation.CanonicalPaths.PhaseStages
import HiddenCircuits.Approximation.CanonicalPaths.BlockRotation
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! Exact finite enumeration of the relative-permutation orbit comprising an
actual component of the union of two matchings. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
variable {n : ℕ}

def relative (p q : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := q.trans p.symm

@[simp] theorem relative_apply (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    p (relative p q i)=q i := by simp [relative]

theorem reachable_relative (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (unionGraph p q).Reachable i (relative p q i) :=
  reachable_of_cross (Or.inr (relative_apply p q i).symm)

theorem sameCycle_of_adj (p q : Equiv.Perm (Fin n)) {i j : Fin n}
    (h : (unionGraph p q).Adj i j) : (relative p q).SameCycle i j := by
  rcases crossing_of_adj h with h|h
  · have he : relative p q j=i := p.injective ((relative_apply p q j).trans h.symm)
    rw [← he]
    exact ((Equiv.Perm.SameCycle.refl _ j).apply_right).symm
  · have he : relative p q i=j := p.injective ((relative_apply p q i).trans h)
    rw [← he]
    exact (Equiv.Perm.SameCycle.refl _ i).apply_right

theorem reachable_iff_sameCycle (p q : Equiv.Perm (Fin n)) (i j : Fin n) :
    (unionGraph p q).Reachable i j ↔ (relative p q).SameCycle i j := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Equiv.Perm.SameCycle.refl _ _
    | cons h tail ih => exact (sameCycle_of_adj p q h).trans ih
  · intro h
    obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction k with
    | zero => simpa using SimpleGraph.Reachable.refl i
    | succ k ih =>
      simpa only [pow_succ',Equiv.Perm.mul_apply] using
        ih.trans (reachable_relative p q (((relative p q)^k) i))

noncomputable def componentPeriod (p q : Equiv.Perm (Fin n)) (active : Fin n) : ℕ :=
  Function.minimalPeriod (relative p q) active

theorem componentPeriod_pos (p q : Equiv.Perm (Fin n)) (active : Fin n) :
    0<componentPeriod p q active :=
  Function.minimalPeriod_pos_of_mem_periodicPts ((relative p q).injective.mem_periodicPts active)

theorem componentPeriod_le (p q : Equiv.Perm (Fin n)) (active : Fin n) :
    componentPeriod p q active ≤ n := by
  simpa only [Fintype.card_fin] using
    (Function.minimalPeriod_le_card (f := relative p q) (x := active))

theorem componentPeriod_gt_one (p q : Equiv.Perm (Fin n)) (active : Fin n)
    (hne : p active≠q active) : 1<componentPeriod p q active := by
  have hp := componentPeriod_pos p q active
  have hneone : componentPeriod p q active≠1 := by
    intro h
    have he : relative p q active=active := Function.minimalPeriod_eq_one_iff_isFixedPt.mp h
    exact hne (by simpa only [he] using (relative_apply p q active))
  omega

noncomputable def orbitPoint (p q : Equiv.Perm (Fin n)) (active : Fin n)
    (i : Fin (componentPeriod p q active)) : Fin n := (relative p q)^[i.val] active

theorem orbitPoint_injective (p q : Equiv.Perm (Fin n)) (active : Fin n) :
    Function.Injective (orbitPoint p q active) := by
  intro a b h
  exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod a.isLt b.isLt).mp h)

theorem orbitPoint_reachable (p q : Equiv.Perm (Fin n)) (active : Fin n)
    (i : Fin (componentPeriod p q active)) :
    (unionGraph p q).Reachable active (orbitPoint p q active i) := by
  apply (reachable_iff_sameCycle p q active _).mpr
  change (relative p q).SameCycle active ((relative p q)^[i.val] active)
  rw [← Equiv.Perm.coe_pow]
  exact (Equiv.Perm.SameCycle.refl _ active).pow_right

theorem exists_orbitPoint (p q : Equiv.Perm (Fin n)) (active i : Fin n)
    (h : (unionGraph p q).Reachable active i) :
    ∃j,orbitPoint p q active j=i := by
  obtain ⟨k,hk⟩ := ((reachable_iff_sameCycle p q active i).mp h).exists_nat_pow_eq
  refine ⟨⟨k%componentPeriod p q active,Nat.mod_lt _ (componentPeriod_pos p q active)⟩,?_⟩
  change (relative p q)^[k%Function.minimalPeriod (relative p q) active] active=i
  rw [Function.iterate_mod_minimalPeriod_eq,← Equiv.Perm.coe_pow]
  exact hk

noncomputable def orbitEquiv (p q : Equiv.Perm (Fin n)) (active : Fin n) :
    Fin (componentPeriod p q active) ≃ {i // (unionGraph p q).Reachable active i} :=
  Equiv.ofBijective (fun i => ⟨orbitPoint p q active i,orbitPoint_reachable p q active i⟩)
    ⟨fun _ _ h => orbitPoint_injective p q active (congrArg Subtype.val h),by
      intro i
      obtain ⟨j,hj⟩ := exists_orbitPoint p q active i.val i.property
      exact ⟨j,Subtype.ext hj⟩⟩

theorem orbitPoint_rotate (p q : Equiv.Perm (Fin n)) (active : Fin n)
    (i : Fin (componentPeriod p q active)) :
    orbitPoint p q active (finRotate _ i)=relative p q (orbitPoint p q active i) := by
  letI : NeZero (componentPeriod p q active) := ⟨Nat.ne_of_gt (componentPeriod_pos p q active)⟩
  rw [rotate_apply]
  change (relative p q)^[((i+1).val)] active=relative p q ((relative p q)^[i.val] active)
  have hv : (i+1).val=(i.val+1)%componentPeriod p q active := by
    simp [Fin.val_add,Fin.val_natCast,Nat.add_mod]
  rw [hv]
  change (relative p q)^[(i.val+1)%Function.minimalPeriod (relative p q) active] active=_
  rw [Function.iterate_mod_minimalPeriod_eq]
  exact Function.iterate_succ_apply' _ _ _

end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
