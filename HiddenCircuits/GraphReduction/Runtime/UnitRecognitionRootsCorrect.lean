import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRootsLoop
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentInitialCorrect
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionUmbrellaCorrect

/-! Physical first-passing-root search and its cached residual agree exactly
with the verified list-mask recognizer. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoots
open Complexity DH.Runtime.PairCheck

lemma good_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) (i : Fin n) :
    good (MatrixData.ofGraph G) A i =
      (UnitIntervalBitMasks.read A.toList i &&
        decide (UnitIntervalOrder.ListUmbrella G.graph (UnitIntervalBitRecognition.component G.graph A.toList i))) := by
  rw [good,←UnitRecognitionChoice.read_vector]
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [UnitRecognitionUmbrella.check_reverse_ofGraph_iff,decide_eq_true_eq,
    UnitRecognitionComponent.component_order_ofGraph]

private def firstStep {α : Type*} (p : α → Bool) (b : Option α) (i : α) : Option α :=
  if !b.isSome && p i then some i else b

private lemma fold_first_some {α : Type*} (p : α → Bool) (xs : List α) (a : α) :
    xs.foldl (firstStep p) (some a) = some a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [firstStep,List.foldl_cons] using ih

private lemma fold_first_none {α : Type*} (p : α → Bool) (xs : List α) :
    xs.foldl (firstStep p) none = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons,List.find?_cons]
    cases hp : p x with
    | false => simpa [firstStep,hp] using ih
    | true => simpa [firstStep,hp] using fold_first_some p xs x

private lemma finRange_drop {n i : ℕ} (hi : i<n) :
    (List.finRange n).drop i = ⟨i,hi⟩::(List.finRange n).drop (i+1) := by
  rw [List.drop_eq_getElem_cons (l:=List.finRange n) (i:=i) (by simpa using hi)]
  congr 1
  apply Fin.ext
  simp only [List.finRange,List.getElem_ofFn]

lemma scanFrom_fold {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (i m : ℕ) (b : Best n) :
    scanFrom G A i m b =
      (((List.finRange n).drop i).take m).foldl (fun old v => step G A v old) b := by
  induction m generalizing i b with
  | zero => rfl
  | succ m ih =>
    by_cases hi : i<n
    · rw [scanFrom,dif_pos hi,finRange_drop hi,List.take_succ_cons,List.foldl_cons]
      exact ih (i+1) _
    · have hd : (List.finRange n).drop i = [] := List.drop_eq_nil_iff.mpr (by simp; omega)
      simp [scanFrom,hi,hd]

/-- Exact first-root agreement, including inactive labels and failed trials. -/
theorem find_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) :
    find (MatrixData.ofGraph G) A = UnitIntervalBitRecognition.goodRoot G.graph A.toList := by
  rw [find,scanFrom_fold,List.drop_zero,List.take_of_length_le (by simp)]
  change (List.finRange n).foldl (firstStep (good (MatrixData.ofGraph G) A)) none = _
  rw [fold_first_none]
  simp only [UnitIntervalBitRecognition.goodRoot,UnitIntervalBitMasks.members,List.find?_filter]
  congr 1
  funext i
  simpa using good_ofGraph G A i

/-- The selected physical remaining mask is the exact pure residual step. -/
theorem residual_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) :
    (residual (MatrixData.ofGraph G) A (find (MatrixData.ofGraph G) A)).toList =
      UnitIntervalComponentResidual.step G.graph A.toList := by
  rw [find_ofGraph]
  unfold residual UnitIntervalComponentResidual.step
  cases hr : UnitIntervalBitRecognition.goodRoot G.graph A.toList with
  | none => rfl
  | some root =>
    exact congrArg UnitIntervalBitMasks.State.remaining (UnitRecognitionComponent.component_ofGraph G A root)

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRoots
