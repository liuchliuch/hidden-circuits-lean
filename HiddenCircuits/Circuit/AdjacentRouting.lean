import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-! Explicit adjacent-swap routing on the actual finite wire positions. -/
namespace HiddenCircuits.Circuit
variable {k : ℕ}

def adjacentSwap (i : Fin (k-1)) : Equiv.Perm (Fin k) :=
  Equiv.swap ⟨i.val,by have := i.isLt; omega⟩ ⟨i.val+1,by have := i.isLt; omega⟩

def executeSwaps : List (Fin (k-1)) → Equiv.Perm (Fin k)
  | [] => Equiv.refl _
  | i::w => (adjacentSwap i).trans (executeSwaps w)

/-- Move the wire lo+d left to lo using exactly d descending adjacent swaps. -/
def routeIndices (lo : ℕ) : (d : ℕ) → lo+d<k → List (Fin (k-1))
  | 0,_ => []
  | d+1,h => ⟨lo+d,by omega⟩ :: routeIndices lo d (by omega)

@[simp] theorem routeIndices_length (lo d : ℕ) (h : lo+d<k) :
    (routeIndices lo d h).length=d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [routeIndices,List.length_cons,ih]

lemma execute_route_top (lo d : ℕ) (h : lo+d<k) :
    executeSwaps (routeIndices lo d h) ⟨lo+d,h⟩ = (⟨lo,by omega⟩ : Fin k) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change executeSwaps (routeIndices lo d (by omega))
      (adjacentSwap ⟨lo+d,by omega⟩ ⟨lo+(d+1),h⟩) = _
    have he : adjacentSwap (⟨lo+d,by omega⟩ : Fin (k-1)) ⟨lo+(d+1),h⟩ =
        (⟨lo+d,by omega⟩ : Fin k) := by
      exact Equiv.swap_apply_right _ _
    rw [he]
    exact ih (by omega)

lemma execute_route_below (lo d : ℕ) (h : lo+d<k) (x : Fin k) (hx : x.val<lo) :
    executeSwaps (routeIndices lo d h) x=x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change executeSwaps (routeIndices lo d (by omega)) (adjacentSwap ⟨lo+d,by omega⟩ x)=x
    have he : adjacentSwap (⟨lo+d,by omega⟩ : Fin (k-1)) x=x := by
      apply Equiv.swap_apply_of_ne_of_ne
      · intro he; have := congrArg Fin.val he; change x.val=lo+d at this; omega
      · intro he; have := congrArg Fin.val he; change x.val=(lo+d)+1 at this; omega
    rw [he]
    exact ih (by omega)

/-- Explicit routing from a<b to the adjacent pair a,a+1. -/
def routeBetween (a b : Fin k) (h : a<b) : List (Fin (k-1)) :=
  routeIndices (a.val+1) (b.val-(a.val+1)) (by have := b.isLt; change a.val<b.val at h; omega)

theorem routeBetween_spec (a b : Fin k) (h : a<b) :
    (routeBetween a b h).length = b.val-a.val-1 ∧
    (routeBetween a b h).length ≤ k-1 ∧
    executeSwaps (routeBetween a b h) a=a ∧
    executeSwaps (routeBetween a b h) b=(⟨a.val+1,by have := b.isLt; change a.val<b.val at h; omega⟩ : Fin k) := by
  have hab : a.val<b.val := h
  have he : a.val+1+(b.val-(a.val+1))=b.val := by omega
  have hl : (routeBetween a b h).length=b.val-a.val-1 := by
    unfold routeBetween
    rw [routeIndices_length]
    omega
  refine ⟨hl,?_,?_,?_⟩
  · rw [hl]; have := b.isLt; omega
  · exact execute_route_below _ _ _ a (by omega)
  · have hh := execute_route_top (a.val+1) (b.val-(a.val+1))
      (show a.val+1+(b.val-(a.val+1))<k by rw [he];exact b.isLt)
    convert hh using 1
    apply congrArg
    exact Fin.ext he.symm

theorem executeSwaps_append (w v : List (Fin (k-1))) :
    executeSwaps (w++v) = (executeSwaps w).trans (executeSwaps v) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append,executeSwaps,ih,Equiv.trans_assoc]

/-- Reversing the same literal adjacent swaps implements the inverse route. -/
theorem executeSwaps_reverse (w : List (Fin (k-1))) :
    executeSwaps w.reverse = (executeSwaps w).symm := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.reverse_cons,executeSwaps_append,executeSwaps,ih]
    ext x
    simp [adjacentSwap,Equiv.symm_swap]

theorem execute_route_undo (a b : Fin k) (h : a<b) (x : Fin k) :
    executeSwaps (routeBetween a b h).reverse (executeSwaps (routeBetween a b h) x)=x := by
  rw [executeSwaps_reverse]
  exact Equiv.symm_apply_apply _ _

end HiddenCircuits.Circuit
