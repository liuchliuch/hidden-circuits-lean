import HiddenCircuits.Approximation.CanonicalPaths.CyclePhases

/-! Fresh phase identities for the actual union components. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem unionGraph_swap (p q : Equiv.Perm (Fin n)) : unionGraph q p=unionGraph p q := by
  apply graph_eq_of_sameUnion
  intro i
  exact Set.pair_comm _ _

theorem componentMin_swap (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    componentMin q p i=componentMin p q i := by
  apply componentMin_sameUnion
  intro j
  exact Set.pair_comm _ _

theorem phase_complement (p q : Equiv.Perm (Fin n)) (cut : ℕ) (i : Fin n) :
    ({phasePermutation p q cut i,phasePermutation q p cut i} : Finset (Fin n))={p i,q i} := by
  change ({phaseValue p q cut i,phaseValue q p cut i} : Finset (Fin n))=_
  simp only [phaseValue,componentMin_swap]
  split_ifs
  · exact Finset.pair_comm _ _
  · rfl

theorem componentMin_self (p q : Equiv.Perm (Fin n)) (active : Fin n) :
    componentMin p q (componentMin p q active)=componentMin p q active :=
  componentMin_eq_of_reachable (componentMin_reachable p q active)

theorem phase_before_component (p q : Equiv.Perm (Fin n)) (active i : Fin n)
    (hrep : componentMin p q active=active) (hi : (unionGraph p q).Reachable active i) :
    phasePermutation p q active.val i=p i := by
  have hm : componentMin p q i=active := (componentMin_eq_of_reachable hi).symm.trans hrep
  change phaseValue p q active.val i=_
  simp [phaseValue,hm]

theorem phase_after_component (p q : Equiv.Perm (Fin n)) (active i : Fin n)
    (hrep : componentMin p q active=active) (hi : (unionGraph p q).Reachable active i) :
    phasePermutation p q (active.val+1) i=q i := by
  have hm : componentMin p q i=active := (componentMin_eq_of_reachable hi).symm.trans hrep
  change phaseValue p q (active.val+1) i=_
  simp [phaseValue,hm]

theorem phase_unchanged_outside (p q : Equiv.Perm (Fin n)) (active i : Fin n)
    (hi : ¬(unionGraph p q).Reachable active i) :
    phasePermutation p q (active.val+1) i=phasePermutation p q active.val i := by
  have hne : componentMin p q i≠active := by
    intro h
    exact hi (h ▸ componentMin_reachable p q i)
  have hval : (componentMin p q i).val≠active.val := fun h => hne (Fin.ext h)
  change phaseValue p q (active.val+1) i=phaseValue p q active.val i
  have hc : (componentMin p q i).val<active.val+1 ↔ (componentMin p q i).val<active.val := by omega
  simp only [phaseValue,hc]

theorem phase_unchanged_nonrepresentative (p q : Equiv.Perm (Fin n)) (active : Fin n)
    (hrep : componentMin p q active≠active) :
    phasePermutation p q (active.val+1)=phasePermutation p q active.val := by
  apply Equiv.ext
  intro i
  have hne : componentMin p q i≠active := by
    intro he
    have hid := componentMin_self p q i
    rw [he] at hid
    exact hrep hid
  have hval : (componentMin p q i).val≠active.val := fun h => hne (Fin.ext h)
  change phaseValue p q (active.val+1) i=phaseValue p q active.val i
  have hc : (componentMin p q i).val<active.val+1 ↔ (componentMin p q i).val<active.val := by omega
  simp only [phaseValue,hc]

theorem reachable_from_fixed (p q : Equiv.Perm (Fin n)) (active i : Fin n)
    (hfix : p active=q active) (h : (unionGraph p q).Reachable active i) : i=active := by
  have hn : ∀j,¬(unionGraph p q).Adj active j := by
    intro j hj
    rcases crossing_of_adj hj with he|he
    · exact hj.1 (q.injective (hfix.symm.trans he))
    · exact hj.1 (p.injective (hfix.trans he))
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons he _ => exact False.elim (hn _ he)

theorem phase_unchanged_fixed (p q : Equiv.Perm (Fin n)) (active : Fin n)
    (hfix : p active=q active) :
    phasePermutation p q (active.val+1)=phasePermutation p q active.val := by
  apply Equiv.ext
  intro i
  by_cases hi : (unionGraph p q).Reachable active i
  · have he := reachable_from_fixed p q active i hfix hi
    subst i
    change phaseValue p q (active.val+1) active=phaseValue p q active.val active
    simp only [phaseValue,← hfix,ite_self]
  · exact phase_unchanged_outside p q active i hi

end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
