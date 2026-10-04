import HiddenCircuits.Approximation.CanonicalPaths.MountainFromPath
import HiddenCircuits.Approximation.CanonicalPaths.MountainClimbing
import HiddenCircuits.Approximation.CanonicalPaths.TokenLocalRoute

/-! Fresh literal two-side mountain extracted from a maximum-started cycle. -/
namespace HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
open MountainSystem
variable {n : ℕ} [NeZero n] {E : MonotoneEndpoints n} (D : CyclePresentation E)

def leftIndex (k : Fin n) (i : Fin (k.val+1)) : Fin n := ⟨i.val,by have := i.isLt; have := k.isLt; omega⟩

def rightIndex (k : Fin n) (hk : 0 < k.val) (i : Fin (n-k.val+1)) : Fin n :=
  if h : i.val=0 then 0 else ⟨n-i.val,by have := i.isLt; have := k.isLt; omega⟩

theorem leftIndex_injective (k : Fin n) : Function.Injective (leftIndex k) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin n => x.val) h)

theorem rightIndex_injective (k : Fin n) (hk : 0 < k.val) : Function.Injective (rightIndex k hk) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hkn := k.isLt
  have hv := congrArg (fun x : Fin n => x.val) h
  by_cases hi₀ : i.val=0 <;> by_cases hj₀ : j.val=0 <;>
    simp only [rightIndex,hi₀,hj₀,↓reduceDIte,Fin.val_zero] at hv <;> omega

@[simp] theorem leftIndex_zero (k : Fin n) : leftIndex k 0=0 := rfl
@[simp] theorem leftIndex_last (k : Fin n) : leftIndex k (Fin.last k.val)=k := by apply Fin.ext; rfl
@[simp] theorem rightIndex_zero (k : Fin n) (hk : 0 < k.val) : rightIndex k hk 0=0 := by simp [rightIndex]
@[simp] theorem rightIndex_last (k : Fin n) (hk : 0 < k.val) : rightIndex k hk (Fin.last (n-k.val))=k := by
  have hkn := k.isLt
  have hn : n-k.val≠0 := by omega
  apply Fin.ext
  simp only [rightIndex,Fin.val_last,hn,↓reduceDIte]
  omega

def rowHeight (i : Fin n) : ℕ := n-1-(D.rows i).val

theorem rowHeight_injective : Function.Injective (rowHeight D) := by
  intro i j h
  apply D.rows.injective
  apply Fin.ext
  have hi := (D.rows i).isLt
  have hj := (D.rows j).isLt
  dsimp [rowHeight] at h
  omega

theorem rowHeight_bound (i : Fin n) : (rowHeight D) i ≤ n-1 := Nat.sub_le _ _

def leftHeights (k : Fin n) (i : Fin (k.val+1)) : ℕ := (rowHeight D) (leftIndex k i)
def rightHeights (k : Fin n) (hk : 0 < k.val) (i : Fin (n-k.val+1)) : ℕ := (rowHeight D) (rightIndex k hk i)

variable (k : Fin n) (hk : 0 < k.val)
  (hmax : (D.rows 0).val=n-1) (hmin : D.rows k=0)

def leftSide : Side (Fin k.val) (n-1) :=
  ofVertices hk ((leftHeights D) k)
    ((rowHeight_injective D).comp (leftIndex_injective k))
    (by simp [leftHeights,rowHeight,hmax])
    (by simp [leftHeights,rowHeight,hmin])
    (fun i => (rowHeight_bound D) _)

def rightSide : Side (Fin (n-k.val)) (n-1) :=
  ofVertices (by have := k.isLt; omega) ((rightHeights D) k hk)
    ((rowHeight_injective D).comp (rightIndex_injective k hk))
    (by simp [rightHeights,rowHeight,hmax])
    (by simp [rightHeights,rowHeight,hmin])
    (fun i => (rowHeight_bound D) _)

include hmax hmin in
theorem heights_separated (i : Fin (k.val+1)) (j : Fin (n-k.val+1))
    (h : (leftHeights D) k i=(rightHeights D) k hk j) :
    (leftHeights D) k i=0 ∨ (leftHeights D) k i=n-1 := by
  have he : leftIndex k i=rightIndex k hk j := (rowHeight_injective D) h
  by_cases hj : j.val=0
  · have hr : rightIndex k hk j=0 := by simp [rightIndex,hj]
    left
    change (rowHeight D) (leftIndex k i)=0
    rw [he,hr]
    simp [rowHeight,hmax]
  · have hi := i.isLt
    have hjb := j.isLt
    have hkn := k.isLt
    have hv := congrArg (fun x : Fin n => x.val) he
    simp only [leftIndex,rightIndex,hj,↓reduceDIte] at hv
    have hik : leftIndex k i=k := Fin.ext (by dsimp [leftIndex]; omega)
    right
    change (rowHeight D) (leftIndex k i)=n-1
    rw [hik]
    simp [rowHeight,hmin]

theorem sides_separated : Separated ((leftSide D) k hk hmax hmin) ((rightSide D) k hk hmax hmin) := by
  intro e f u v h
  exact (heights_separated D) k hk hmax hmin (MountainSide.node (e,u)) (MountainSide.node (f,v)) h

end HiddenCircuits.Approximation.CanonicalPaths.CycleMountain
