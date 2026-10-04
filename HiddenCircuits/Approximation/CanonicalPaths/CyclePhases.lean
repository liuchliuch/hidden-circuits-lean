import HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
import HiddenCircuits.Approximation.CanonicalPaths.LocalRoutes
namespace HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
attribute [local instance] Classical.propDecidable
variable {n : ℕ}
noncomputable def componentVertices (p q : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (unionGraph p q).Reachable i j)
theorem componentVertices_nonempty (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (componentVertices p q i).Nonempty := by
  refine ⟨i,?_⟩
  simp [componentVertices,SimpleGraph.Reachable.refl]
noncomputable def componentMin (p q : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  (componentVertices p q i).min' (componentVertices_nonempty p q i)
theorem componentMin_reachable (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (unionGraph p q).Reachable (componentMin p q i) i := by
  have h := Finset.min'_mem (componentVertices p q i) (componentVertices_nonempty p q i)
  simp only [componentVertices,Finset.mem_filter,Finset.mem_univ,true_and] at h
  exact h.symm
theorem componentMin_eq_of_reachable {p q : Equiv.Perm (Fin n)} {i j : Fin n}
    (h : (unionGraph p q).Reachable i j) : componentMin p q i=componentMin p q j := by
  have hs : componentVertices p q i=componentVertices p q j := by
    ext v
    simp only [componentVertices,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun hv => h.symm.trans hv,fun hv => h.trans hv⟩
  unfold componentMin
  simp only [hs]
theorem componentMin_sameUnion {p q r s : Equiv.Perm (Fin n)} (h : SameUnion p q r s)
    (i : Fin n) : componentMin p q i=componentMin r s i := by
  have hs : componentVertices p q i=componentVertices r s i := by
    unfold componentVertices
    rw [graph_eq_of_sameUnion h]
  unfold componentMin
  simp only [hs]
theorem reachable_of_cross {p q : Equiv.Perm (Fin n)} {i j : Fin n}
    (h : p i=q j ∨ q i=p j) : (unionGraph p q).Reachable i j := by
  by_cases hij : i=j
  · subst j
    exact SimpleGraph.Reachable.refl _
  apply SimpleGraph.Adj.reachable
  refine ⟨hij,?_⟩
  rcases h with h|h
  · exact ⟨p i,by simp,by simp [h]⟩
  · exact ⟨q i,by simp,by simp [h]⟩
noncomputable def phaseValue (p q : Equiv.Perm (Fin n)) (cut : ℕ) (i : Fin n) : Fin n :=
  if (componentMin p q i).val<cut then q i else p i
theorem phaseValue_injective (p q : Equiv.Perm (Fin n)) (cut : ℕ) :
    Function.Injective (phaseValue p q cut) := by
  intro i j h
  unfold phaseValue at h
  split_ifs at h with hi hj hj
  · exact q.injective h
  · have hre := reachable_of_cross (p := p) (q := q) (Or.inr h)
    have hm := componentMin_eq_of_reachable hre
    exact False.elim (hj (hm ▸ hi))
  · have hre := reachable_of_cross (p := p) (q := q) (Or.inl h)
    have hm := componentMin_eq_of_reachable hre
    exact False.elim (hi (hm.symm ▸ hj))
  · exact p.injective h
noncomputable def phasePermutation (p q : Equiv.Perm (Fin n)) (cut : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (phaseValue p q cut)
    ⟨phaseValue_injective p q cut,Finite.surjective_of_injective (phaseValue_injective p q cut)⟩
@[simp] theorem phasePermutation_zero (p q : Equiv.Perm (Fin n)) : phasePermutation p q 0=p := by
  apply Equiv.ext
  intro i
  simp [phasePermutation,phaseValue]
@[simp] theorem phasePermutation_full (p q : Equiv.Perm (Fin n)) : phasePermutation p q n=q := by
  apply Equiv.ext
  intro i
  simp [phasePermutation,phaseValue,(componentMin p q i).isLt]
noncomputable def phaseState {R : Fin n → Fin n → Prop} (p q : LocalRoutes.State R) (cut : ℕ) :
    LocalRoutes.State R := by
  refine ⟨phasePermutation p.val q.val cut,?_⟩
  intro i
  change R i (if (componentMin p.val q.val i).val<cut then q.val i else p.val i)
  split_ifs
  · exact q.property i
  · exact p.property i
def Interrupted (p q z : Equiv.Perm (Fin n)) (active : Fin n) : Prop :=
  ∀ i, ¬(unionGraph p q).Reachable active i → z i=phasePermutation p q active.val i
theorem reconstruct_interrupted {p q r s z : Equiv.Perm (Fin n)} {active : Fin n}
    (hU : SameUnion p q r s) (hp : Interrupted p q z active) (hr : Interrupted r s z active)
    (horient : r active=p active) : p=r ∧ q=s := by
  apply determined_by_representatives hU
  intro j
  by_cases hreach : (unionGraph p q).Reachable active j
  · exact ⟨active,hreach,horient⟩
  have hreach' : ¬(unionGraph r s).Reachable active j := by rwa [← graph_eq_of_sameUnion hU]
  have h₁ := hp j hreach
  have h₂ := hr j hreach'
  change z j=phaseValue p q active.val j at h₁
  change z j=phaseValue r s active.val j at h₂
  have hm := componentMin_sameUnion hU j
  unfold phaseValue at h₁ h₂
  rw [← hm] at h₂
  by_cases hc : (componentMin p q j).val<active.val
  · simp only [if_pos hc] at h₁ h₂
    exact ⟨j,SimpleGraph.Reachable.refl _,left_eq_of_right_eq hU (h₂.symm.trans h₁)⟩
  · simp only [if_neg hc] at h₁ h₂
    exact ⟨j,SimpleGraph.Reachable.refl _,h₂.symm.trans h₁⟩
end HiddenCircuits.Approximation.CanonicalPaths.UnionReconstruction
