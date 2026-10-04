import HiddenCircuits.Approximation.CanonicalPaths.CycleConfigurations
import HiddenCircuits.Approximation.CanonicalPaths.CycleExtremeFocus
import HiddenCircuits.Approximation.CanonicalPaths.TokenBoundaries

/-! Unconditional concrete middle route for a maximum-started alternating cycle.
The only inputs are its literal endpoint edges and its maximum-row convention. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
open MountainSystem LocalRoutes
variable {n : ℕ} {E : MonotoneEndpoints n}

theorem cycle_middle_route (D : CyclePresentation E) (hn : 1<n)
    (hmax : (D.rows ⟨0,by omega⟩).val=n-1) :
    ∃ Z0 Z1 : State (fun col row => Allowed E row col),
      (∃S : Finset (Fin n),S.card ≤ 2 ∧ ∀i,i∉S → Z0.val i=D.source.val i) ∧
      (∃T : Finset (Fin n),T.card ≤ 2 ∧ ∀i,i∉T → Z1.val i=D.target.val i) ∧
      ∃l < 8*n*n,MarkedRoute Finset.univ (fun Z => HasCompanion D.source D.target Z 6) Z0 Z1 l := by
  letI : NeZero n := ⟨by omega⟩
  change (D.rows (0 : Fin n)).val=n-1 at hmax
  let k : Fin n := D.rows.symm 0
  have hmin : D.rows k=0 := D.rows.apply_symm_apply _
  have hk : 0 < k.val := by
    by_contra h
    have he : k=0 := Fin.ext (by simpa only [Fin.val_zero] using Nat.eq_zero_of_not_pos h)
    rw [he] at hmin
    have hv := congrArg Fin.val hmin
    simp only [Fin.val_zero] at hv
    omega
  let A := leftSide D k hk hmax hmin
  let B := rightSide D k hk hmax hmin
  obtain ⟨l,hl,hr⟩ := middle_at_minimum D k hk hmax hmin
  refine ⟨stateAt D k hk hmax hmin (bottomPort A B),stateAt D k hk hmax hmin (topPort A B),?_,?_,l,hl,hr⟩
  · exact D.primary_boundary_source _ _ _ _
      (bottom_focusLeft D k hk hmax hmin) (bottom_focusRight D k hk hmax hmin)
  · exact D.primary_boundary_target _ _ _ _ (top_focus_adjacent D k hk hmax hmin)

end HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
