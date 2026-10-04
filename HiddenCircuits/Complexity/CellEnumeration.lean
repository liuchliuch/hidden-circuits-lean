import HiddenCircuits.Complexity.TM2PortArithmetic
import Mathlib.Data.List.OfFn

/-! Exact ordered traversal of the actual Boolean cell numbering: first control
bits, then each stack position and the fixed symbol family at that position. -/
namespace HiddenCircuits.Complexity.TM2BooleanEncoding

lemma cellEnumeration_symm_control (M : Turing.FinTM2) (H : ℕ) (i : Fin (controlBits M)) :
    (cellEnumeration M H).symm (i.castAdd (H*symbolBits M)) =
      Sum.inl ((Fintype.equivFin (Control M)).symm i) := by
  apply (cellEnumeration M H).symm_apply_eq.mpr
  apply Fin.ext
  simp [cellEnumeration_control_val]

lemma cellEnumeration_symm_stack (M : Turing.FinTM2) (H : ℕ) (i : Fin H) (a : Fin (symbolBits M)) :
    (cellEnumeration M H).symm ((finProdFinEquiv (i,a)).natAdd (controlBits M)) =
      Sum.inr ⟨((symbolEnumeration M).symm a).1,(i,((symbolEnumeration M).symm a).2)⟩ := by
  apply (cellEnumeration M H).symm_apply_eq.mpr
  apply Fin.ext
  rw [cellEnumeration_stack_val]
  simp only [Fin.val_natAdd,finProdFinEquiv,Equiv.coe_fn_mk,Sigma.eta,Equiv.apply_symm_apply]
  ring

/-- An exact list identity for arbitrary cell payloads, so clause and bitstream
traversals use the same explicit arithmetic enumeration. -/
theorem ofFn_cells {α : Type*} (M : Turing.FinTM2) (H : ℕ) (F : Cell M H → α) :
    List.ofFn (fun i : Fin (bitCount M H) => F ((cellEnumeration M H).symm i)) =
      List.ofFn (fun i : Fin (controlBits M) => F (Sum.inl ((Fintype.equivFin (Control M)).symm i))) ++
      (List.ofFn (fun i : Fin H => List.ofFn (fun a : Fin (symbolBits M) =>
        F (Sum.inr ⟨((symbolEnumeration M).symm a).1,(i,((symbolEnumeration M).symm a).2)⟩)))).flatten := by
  change List.ofFn (fun i : Fin (controlBits M+H*symbolBits M) => F ((cellEnumeration M H).symm i)) = _
  rw [List.ofFn_add]
  apply congrArg₂ List.append
  · apply congrArg List.ofFn
    funext i
    rw [show i.castLE (Nat.le_add_right (controlBits M) (H*symbolBits M)) = i.castAdd (H*symbolBits M) from rfl]
    rw [cellEnumeration_symm_control]
  · rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    apply congrArg List.ofFn
    funext a
    have hh : i.val*symbolBits M+a.val < H*symbolBits M := by
      have h := (finProdFinEquiv (i,a)).isLt
      simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using h
    have he : (⟨i.val*symbolBits M+a.val,hh⟩ : Fin (H*symbolBits M)) = finProdFinEquiv (i,a) := by
      apply Fin.ext
      change i.val*symbolBits M+a.val = a.val+symbolBits M*i.val
      ring
    rw [he,cellEnumeration_symm_stack]

end HiddenCircuits.Complexity.TM2BooleanEncoding
