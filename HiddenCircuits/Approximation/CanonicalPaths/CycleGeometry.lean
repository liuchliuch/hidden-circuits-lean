import HiddenCircuits.Approximation.CanonicalPaths.CycleMountain

/-! Fresh exact interpretation of mountain edges as actual cycle focus columns. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
open MountainSystem
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n}

def leftFocus (k : Fin n) (e : Fin k.val) : Fin n := ⟨e.val,e.isLt.trans k.isLt⟩
def rightFocus (k : Fin n) (f : Fin (n-k.val)) : Fin n := ⟨n-1-f.val,by have := k.isLt; omega⟩

theorem focus_ordered (k : Fin n) (e : Fin k.val) (f : Fin (n-k.val)) : leftFocus k e < rightFocus k f := by
  change e.val < n-1-f.val
  have he := e.isLt
  have hf := f.isLt
  have hk := k.isLt
  omega

theorem rotate_last_value (i : Fin n) (hi : i.val=n-1) : finRotate n i=0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
    have he : i=Fin.last m := Fin.ext (by simpa using hi)
    rw [he,finRotate_last]

variable (D : CyclePresentation E) (k : Fin n) (hk : 0 < k.val)
  (hmax : (D.rows 0).val=n-1) (hmin : D.rows k=0)

@[simp] theorem left_height_false (e : Fin k.val) :
    (leftSide D k hk hmax hmin).height e false=rowHeight D (leftFocus k e) := rfl

@[simp] theorem left_height_true (e : Fin k.val) :
    (leftSide D k hk hmax hmin).height e true=rowHeight D (finRotate n (leftFocus k e)) := by
  change rowHeight D (leftIndex k e.succ)=_
  apply congrArg (rowHeight D)
  apply Fin.ext
  have ha : (leftFocus k e).val+1 < n := by
    have he := e.isLt
    have hkn := k.isLt
    change e.val+1 < n
    omega
  rw [rotate_apply,Fin.val_add_one_of_lt' ha]
  rfl

@[simp] theorem right_height_false (f : Fin (n-k.val)) :
    (rightSide D k hk hmax hmin).height f false=rowHeight D (finRotate n (rightFocus k f)) := by
  change rowHeight D (rightIndex k hk f.castSucc)=_
  apply congrArg (rowHeight D)
  have hf := f.isLt
  have hkn := k.isLt
  by_cases h : f.val=0
  · have hr : (rightFocus k f).val=n-1 := by simp [rightFocus,h]
    rw [rotate_last_value _ hr]
    simp [rightIndex,h]
  · have ha : (rightFocus k f).val+1 < n := by dsimp [rightFocus]; omega
    apply Fin.ext
    rw [rotate_apply,Fin.val_add_one_of_lt' ha]
    simp only [rightIndex,Fin.val_castSucc,h,↓reduceDIte,rightFocus]
    omega

@[simp] theorem right_height_true (f : Fin (n-k.val)) :
    (rightSide D k hk hmax hmin).height f true=rowHeight D (rightFocus k f) := by
  change rowHeight D (rightIndex k hk f.succ)=_
  apply congrArg (rowHeight D)
  apply Fin.ext
  have hf := f.isLt
  have hkn := k.isLt
  simp only [rightIndex,Fin.val_succ,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceDIte,rightFocus]
  omega

abbrev CyclePort := Port (leftSide D k hk hmax hmin) (rightSide D k hk hmax hmin)

def focusLeft (p : CyclePort D k hk hmax hmin) : Fin n := leftFocus k p.1.val.1
def focusRight (p : CyclePort D k hk hmax hmin) : Fin n := rightFocus k p.1.val.2

theorem focus_overlap (p : CyclePort D k hk hmax hmin) :
    D.FocusOverlap (focusLeft D k hk hmax hmin p) (focusRight D k hk hmax hmin p) := by
  have h := p.1.property
  change MountainIntervals.Overlap
    ((leftSide D k hk hmax hmin).height p.1.val.1 false)
    ((leftSide D k hk hmax hmin).height p.1.val.1 true)
    ((rightSide D k hk hmax hmin).height p.1.val.2 false)
    ((rightSide D k hk hmax hmin).height p.1.val.2 true) at h
  rw [left_height_false,left_height_true,right_height_false,right_height_true] at h
  have h₀ := (D.rows (leftFocus k p.1.val.1)).isLt
  have h₁ := (D.rows (finRotate n (leftFocus k p.1.val.1))).isLt
  have h₂ := (D.rows (rightFocus k p.1.val.2)).isLt
  have h₃ := (D.rows (finRotate n (rightFocus k p.1.val.2))).isLt
  unfold MountainIntervals.Overlap MountainIntervals.lower MountainIntervals.upper rowHeight at h
  unfold CyclePresentation.FocusOverlap focusLeft focusRight
  simp only [Fin.le_iff_val_le_val,Fin.coe_min,Fin.coe_max]
  omega

end HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
