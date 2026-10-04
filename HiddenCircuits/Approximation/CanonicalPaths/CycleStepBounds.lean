import HiddenCircuits.Approximation.CanonicalPaths.CycleGeometry
import HiddenCircuits.Approximation.CanonicalPaths.MountainStepBounds

/-! Fresh cycle-index bounds for every actual mountain graph edge. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
open MountainSystem
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n} (D : CyclePresentation E)
  (k : Fin n) (hk : 0 < k.val) (hmax : (D.rows 0).val=n-1) (hmin : D.rows k=0)

local notation "A" => leftSide D k hk hmax hmin
local notation "B" => rightSide D k hk hmax hmin
local notation "sep" => sides_separated D k hk hmax hmin

theorem focus_step {p q : CyclePort D k hk hmax hmin} (h : (eventGraph A B sep).Adj p q) :
    (focusLeft D k hk hmax hmin p).val ≤ (focusLeft D k hk hmax hmin q).val+1 ∧
    (focusLeft D k hk hmax hmin q).val ≤ (focusLeft D k hk hmax hmin p).val+1 ∧
    (focusRight D k hk hmax hmin p).val ≤ (focusRight D k hk hmax hmin q).val+1 ∧
    (focusRight D k hk hmax hmin q).val ≤ (focusRight D k hk hmax hmin p).val+1 := by
  have ha : ∀p : Fin k.val × Bool,(leftFocus k ((A).mate p).1).val ≤ (leftFocus k p.1).val+1 ∧
      (leftFocus k p.1).val ≤ (leftFocus k ((A).mate p).1).val+1 := by
    intro p
    exact MountainSide.mate_edge_distance p
  have hb : ∀p : Fin (n-k.val) × Bool,(rightFocus k ((B).mate p).1).val ≤ (rightFocus k p.1).val+1 ∧
      (rightFocus k p.1).val ≤ (rightFocus k ((B).mate p).1).val+1 := by
    intro p
    have hp := p.1.isLt
    have hq := (MountainSide.mate p).1.isLt
    have hh := MountainSide.mate_edge_distance p
    change n-1-(MountainSide.mate p).1.val ≤ n-1-p.1.val+1 ∧
      n-1-p.1.val ≤ n-1-(MountainSide.mate p).1.val+1
    omega
  exact event_step_bounds A B sep (fun e => (leftFocus k e).val) (fun f => (rightFocus k f).val) ha hb h

end HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
