import HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
import Mathlib.Algebra.Group.Fin.Basic

/-! Rotating the cycle enumeration preserves the actual matching endpoints. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
open LocalRoutes
variable {n : ℕ} {E : MonotoneEndpoints n}

noncomputable def reindex (D : CyclePresentation E) (σ : Equiv.Perm (Fin n))
    (hσ : ∀i,σ (finRotate n i)=finRotate n (σ i)) : CyclePresentation E where
  rows := σ.trans D.rows
  columns := σ.trans D.columns
  sourceEdges i := D.sourceEdges (σ i)
  targetEdges i := by
    change Allowed E (D.rows (σ (finRotate n i))) (D.columns (σ i))
    rw [hσ]
    exact D.targetEdges (σ i)

@[simp] theorem reindex_source (D : CyclePresentation E) (σ : Equiv.Perm (Fin n))
    (hσ : ∀i,σ (finRotate n i)=finRotate n (σ i)) : (D.reindex σ hσ).source=D.source := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  simp [source,state,reindex]

@[simp] theorem reindex_target (D : CyclePresentation E) (σ : Equiv.Perm (Fin n))
    (hσ : ∀i,σ (finRotate n i)=finRotate n (σ i)) : (D.reindex σ hσ).target=D.target := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  simp only [target,state,reindex,Equiv.trans_apply,Equiv.symm_trans_apply]
  rw [hσ]
  simp

theorem shift_commutes [NeZero n] (t i : Fin n) :
    Equiv.addRight t (finRotate n i)=finRotate n (Equiv.addRight t i) := by
  simp only [Equiv.coe_addRight,rotate_apply]
  ac_rfl

/-- The maximum row is moved to cycle index zero without changing either matching. -/
theorem exists_maximum_start (D : CyclePresentation E) (hn : 0<n) :
    ∃D' : CyclePresentation E,D'.source=D.source ∧ D'.target=D.target ∧
      (D'.rows ⟨0,hn⟩).val=n-1 := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let maxrow : Fin n := ⟨n-1,by omega⟩
  let t := D.rows.symm maxrow
  refine ⟨D.reindex (Equiv.addRight t) (shift_commutes t),reindex_source _ _ _,reindex_target _ _ _,?_⟩
  change (D.rows (Equiv.addRight t ⟨0,hn⟩)).val=n-1
  have hz : (⟨0,hn⟩ : Fin n)=0 := Fin.ext (by simp)
  rw [hz]
  simp [t,maxrow]

end HiddenCircuits.Approximation.CanonicalPaths.CyclePresentation
