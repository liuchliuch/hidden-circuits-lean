import HiddenCircuits.Approximation.CanonicalPaths.BlockSupport

/-! Fresh literal focus-boundary choices and their scalar bounds. -/
namespace HiddenCircuits.Approximation.CanonicalPaths
variable {n : ℕ}

def preceding (b : Fin n) (hb : 0 < b.val) : Fin n := ⟨b.val-1,by have := b.isLt; omega⟩
def rightCut (b : Fin n) (hb : 0 < b.val) (next : Bool) : Fin n := if next then b else preceding b hb
def leftCut (a : Fin n) (next : Bool) : Fin n := if next then finRotate n a else a

theorem rotate_preceding [NeZero n] (b : Fin n) (hb : 0 < b.val) : finRotate n (preceding b hb)=b := by
  apply Fin.ext
  rw [rotate_apply,Fin.val_add_one_of_lt' (by dsimp [preceding]; have := b.isLt; omega)]
  dsimp [preceding]
  omega

theorem rotate_rightCut [NeZero n] (b : Fin n) (hb : 0 < b.val) (next : Bool) :
    finRotate n (rightCut b hb next)=if next then finRotate n b else b := by
  cases next <;> simp [rightCut,rotate_preceding]

theorem rightCut_bounds (b : Fin n) (hb : 0 < b.val) (next : Bool) :
    b.val-1 ≤ (rightCut b hb next).val ∧ (rightCut b hb next).val ≤ b.val := by
  cases next <;> simp [rightCut,preceding]

theorem leftCut_bounds [NeZero n] (a b : Fin n) (hab : a < b) (next : Bool) :
    a.val ≤ (leftCut a next).val ∧ (leftCut a next).val ≤ a.val+1 := by
  have ha : a.val+1 < n := by have := b.isLt; change a.val < b.val at hab; omega
  cases next <;> simp [leftCut,rotate_apply,Fin.val_add_one_of_lt' ha]

theorem left_le_rightCut (a b : Fin n) (hab : a < b) (next : Bool) :
    a ≤ rightCut b (by change a.val < b.val at hab; omega) next := by
  have h := rightCut_bounds b (by change a.val < b.val at hab; omega) next
  change a.val ≤ _
  change a.val < b.val at hab
  omega

theorem leftCut_le_right [NeZero n] (a b : Fin n) (hab : a < b) (next : Bool) : leftCut a next ≤ b := by
  have h := leftCut_bounds a b hab next
  change _ ≤ b.val
  change a.val < b.val at hab
  omega

def chooseSecond (lower : Bool) (x y : Fin n) : Bool :=
  if lower then decide (y ≤ x) else decide (x ≤ y)

theorem chosen_extreme (lower : Bool) (x y : Fin n) :
    (if chooseSecond lower x y then y else x)=if lower then min x y else max x y := by
  cases lower
  · by_cases h : x ≤ y
    · simp [chooseSecond,h,max_eq_right h]
    · simp [chooseSecond,h,max_eq_left (le_of_not_ge h)]
  · by_cases h : y ≤ x
    · simp [chooseSecond,h,min_eq_right h]
    · simp [chooseSecond,h,min_eq_left (le_of_not_ge h)]


end HiddenCircuits.Approximation.CanonicalPaths
