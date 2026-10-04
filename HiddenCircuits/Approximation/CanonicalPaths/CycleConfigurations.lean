import HiddenCircuits.Approximation.CanonicalPaths.CycleStepBounds

/-! Fresh legal matching state at every mountain port and its marked local route. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
open MountainSystem LocalRoutes
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n} (D : CyclePresentation E)
  (k : Fin n) (hk : 0 < k.val) (hmax : (D.rows 0).val=n-1) (hmin : D.rows k=0)

local notation "A" => leftSide D k hk hmax hmin
local notation "B" => rightSide D k hk hmax hmin
local notation "sep" => sides_separated D k hk hmax hmin

def stateAt (p : CyclePort D k hk hmax hmin) : State (fun col row => Allowed E row col) :=
  D.primary (focusLeft D k hk hmax hmin p) (focusRight D k hk hmax hmin p)
    (focus_ordered k p.1.val.1 p.1.val.2) (focus_overlap D k hk hmax hmin p)

theorem stateAt_companion (p : CyclePort D k hk hmax hmin) :
    HasCompanion D.source D.target (stateAt D k hk hmax hmin p) 2 :=
  D.primary_hasCompanion _ _ _ _

theorem stateAt_neighboring {p q : CyclePort D k hk hmax hmin} (h : (eventGraph A B sep).Adj p q) :
    ∃l ≤ 4,MarkedRoute Finset.univ (fun Z => HasCompanion D.source D.target Z 6)
      (stateAt D k hk hmax hmin p) (stateAt D k hk hmax hmin q) l := by
  have hs := focus_step D k hk hmax hmin h
  exact D.neighboring_route _ _ _ _ _ _ _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

/-- The literal mountain walk yields an actual matching route with six repairs. -/
theorem middle_at_minimum : ∃l < 8*n*n,
    MarkedRoute Finset.univ (fun Z => HasCompanion D.source D.target Z 6)
      (stateAt D k hk hmax hmin (bottomPort A B))
      (stateAt D k hk hmax hmin (topPort A B)) l := by
  obtain ⟨w,hw⟩ := exists_bounded_climb A B sep
  simp only [Fintype.card_fin] at hw
  obtain ⟨l,hl,hr⟩ := marked_route_of_walk (stateAt D k hk hmax hmin)
    (fun Z => HasCompanion D.source D.target Z 6) 4
    (fun p => (stateAt_companion D k hk hmax hmin p).mono (by omega))
    (fun p q h => stateAt_neighboring D k hk hmax hmin h) w
  have hprod : k.val*(n-k.val) ≤ n*n := Nat.mul_le_mul k.isLt.le (Nat.sub_le _ _)
  exact ⟨l,by nlinarith,hr⟩

end HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
