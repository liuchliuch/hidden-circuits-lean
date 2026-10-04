import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentInitialize
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentCorrect
import HiddenCircuits.GraphReduction.UnitIntervalComponentResidual

/-! The full initialized physical component call has exactly the verified
Boolean-list component semantics, including its reusable remaining mask. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity DH.Runtime.PairCheck

lemma false_mask_active (n : ℕ) :
    UnitIntervalBitMasks.active (List.replicate n false) = (∅ : Finset (Fin n)) := by
  ext v
  simp [UnitIntervalBitMasks.active,UnitIntervalBitMasks.read,v.isLt]

lemma singleton_mask {n : ℕ} (root : Fin n) :
    (List.replicate n false).set root.val true = UnitIntervalBitMasks.ofFinset {root} := by
  apply UnitIntervalComponentResidual.mask_ext (n:=n)
  · simp
  · simp
  · change UnitIntervalBitMasks.active (UnitIntervalBitMasks.set (List.replicate n false) root true) = _
    rw [UnitIntervalBitMasks.active_set_true _ (by simp),false_mask_active,UnitIntervalBitMasks.active_ofFinset]
    simp

lemma initial_toLists {n : ℕ} (A : Vector Bool n) (root : Fin n) :
    toLists (initial A root) =
      (⟨[root],UnitIntervalBitMasks.ofFinset {root},UnitIntervalBitMasks.set A.toList root false⟩ :
        UnitIntervalBitMasks.State n) := by
  simp [toLists,initial,emptyData,advance,Vector.toList_set,UnitIntervalBitMasks.set,singleton_mask]

/-- Full physical component semantics, with no supplied ordering certificate. -/
theorem component_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) (root : Fin n) :
    toLists (component (MatrixData.ofGraph G) A root) = UnitIntervalBitRecognition.componentState G.graph A.toList root := by
  rw [component,run_ofGraph,initial_toLists]
  rfl

theorem component_order_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) (root : Fin n) :
    (component (MatrixData.ofGraph G) A root).order = UnitIntervalBitRecognition.component G.graph A.toList root :=
  congrArg UnitIntervalBitMasks.State.order (component_ofGraph G A root)

theorem component_remaining_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) (root : Fin n) :
    (component (MatrixData.ofGraph G) A root).remaining.toList =
      UnitIntervalBitRecognition.eraseList A.toList (UnitIntervalBitRecognition.component G.graph A.toList root) := by
  have h := congrArg UnitIntervalBitMasks.State.remaining (component_ofGraph G A root)
  exact h.trans (UnitIntervalComponentResidual.component_remaining_eq G.graph A.toList (by simp) root)

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
