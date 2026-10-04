import HiddenCircuits.Complexity.BitList
import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! This small independent base
is shared by mask updates and the forthcoming retained-vertex enumeration. -/
namespace HiddenCircuits.Approximation.Initialization.MaskEnumerationSemantics
open Complexity

def mask {n : ℕ} (U : Finset (Fin n)) : BitString := List.ofFn (fun i => decide (i∈U))

@[simp] theorem mask_length {n : ℕ} (U : Finset (Fin n)) : (mask U).length=n := by simp [mask]
@[simp] theorem mask_univ (n : ℕ) : mask (Finset.univ : Finset (Fin n))=List.replicate n true := by simp [mask]

 theorem mask_erase {n : ℕ} (U : Finset (Fin n)) (v : Fin n) :
    mask (U.erase v)=(mask U).set v.val false := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hin : i < n := by simpa using hi
    by_cases he : i=v.val
    · subst i
      simp [mask,Finset.mem_erase]
    · have hne : (⟨i,hin⟩ : Fin n) ≠ v := by intro h; exact he (congrArg Fin.val h)
      simp [mask,List.getElem_set,he,Ne.symm he,hne,Finset.mem_erase]

 theorem set_mask_erase {n : ℕ} (U : Finset (Fin n)) (v : Fin n) :
    (mask U).set v.val false=mask (U.erase v) := (mask_erase U v).symm

end HiddenCircuits.Approximation.Initialization.MaskEnumerationSemantics
