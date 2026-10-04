import HiddenCircuits.Approximation.CanonicalPaths.CycleGeometry

/-! Literal cycle indices at the two extreme mountain cells. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
open MountainSystem
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n}
  (D : CyclePresentation E) (k : Fin n) (hk : 0<k.val)
  (hmax : (D.rows 0).val=n-1) (hmin : D.rows k=0)

@[simp] theorem bottom_focusLeft :
    (focusLeft D k hk hmax hmin
      (bottomPort (leftSide D k hk hmax hmin) (rightSide D k hk hmax hmin))).val=0 := rfl

@[simp] theorem bottom_focusRight :
    (focusRight D k hk hmax hmin
      (bottomPort (leftSide D k hk hmax hmin) (rightSide D k hk hmax hmin))).val=n-1 := by
  change n-1-0=n-1
  omega

@[simp] theorem top_focusLeft :
    (focusLeft D k hk hmax hmin
      (topPort (leftSide D k hk hmax hmin) (rightSide D k hk hmax hmin))).val=k.val-1 := rfl

@[simp] theorem top_focusRight :
    (focusRight D k hk hmax hmin
      (topPort (leftSide D k hk hmax hmin) (rightSide D k hk hmax hmin))).val=k.val := by
  change n-1-(n-k.val-1)=k.val
  have hkn := k.isLt
  omega

theorem top_focus_adjacent :
    (focusRight D k hk hmax hmin
      (topPort (leftSide D k hk hmax hmin) (rightSide D k hk hmax hmin))).val=
    (focusLeft D k hk hmax hmin
      (topPort (leftSide D k hk hmax hmin) (rightSide D k hk hmax hmin))).val+1 := by
  rw [top_focusRight,top_focusLeft]
  omega

end HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
