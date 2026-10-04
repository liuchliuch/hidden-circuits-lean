import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoiceLoop
import HiddenCircuits.GraphReduction.UnitIntervalBitMasks

/-! Exact refinement of the physical vector-mask selector to the verified
Boolean-list first-maximum selector. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
open Complexity DH.Runtime.PairCheck

lemma read_vector {n : ℕ} (A : Vector Bool n) (v : Fin n) :
    UnitIntervalBitMasks.read A.toList v = A[v.val] := by
  simp [UnitIntervalBitMasks.read,List.getElem?_eq_getElem,v.isLt]

lemma hit_ofGraph {n : ℕ} (G : MatrixGraph n) (mask : Vector Bool n) (u x : Fin n) :
    UnitRecognitionScore.hit (MatrixData.ofGraph G) mask u x =
      (UnitIntervalBitMasks.read mask.toList x && decide (UnitIntervalGreedy.ClosedAdj G.graph u x)) := by
  rw [read_vector]
  apply Bool.eq_iff_iff.mpr
  simp only [UnitRecognitionScore.hit,MatrixData.ofGraph,UnitIntervalGreedy.ClosedAdj,
    MatrixGraph.graph,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  exact and_congr_right (fun _ => or_congr eq_comm Iff.rfl)

lemma score_ofGraph {n : ℕ} (G : MatrixGraph n) (mask : Vector Bool n) (u : Fin n) :
    UnitRecognitionScore.score (MatrixData.ofGraph G) mask u =
      UnitIntervalBitMasks.score G.graph mask.toList u := by
  rw [UnitRecognitionScore.score_countP,UnitIntervalBitMasks.score]
  apply List.countP_congr
  intro x _
  rw [hit_ofGraph G mask u x]

lemma step_ofGraph {n : ℕ} (G : MatrixGraph n) (A S R : Vector Bool n) (i : Fin n) (b : Best n) :
    step (MatrixData.ofGraph G) A S R i b =
      UnitIntervalBitMasks.chooseStep G.graph A.toList S.toList R.toList b i := by
  cases b with
  | none =>
    simp [step,prefer,UnitRecognitionBetter.better,selectedScore,UnitIntervalBitMasks.chooseStep,
      UnitIntervalBitMasks.consider,read_vector]
  | some b =>
    have hp : prefer (MatrixData.ofGraph G) A S R (some b) i =
        (R[i.val] && decide (UnitIntervalBitMasks.priority G.graph A.toList S.toList b <
          UnitIntervalBitMasks.priority G.graph A.toList S.toList i)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [prefer,UnitRecognitionBetter.better,selectedScore,Option.map_some,Option.getD_some,
        Option.isSome_some,Bool.not_true,Bool.false_or,score_ofGraph,Bool.and_eq_true,Bool.or_eq_true,
        decide_eq_true_eq,UnitIntervalBitMasks.priority_improves]
      exact and_congr_right (fun _ => or_congr Iff.rfl (and_congr eq_comm Iff.rfl))
    rw [step,hp]
    simp only [UnitIntervalBitMasks.chooseStep,read_vector,UnitIntervalBitMasks.consider]
    cases hR : R[i.val] <;> simp [hR]

private lemma finRange_drop {n i : ℕ} (hi : i<n) :
    (List.finRange n).drop i = ⟨i,hi⟩::(List.finRange n).drop (i+1) := by
  rw [List.drop_eq_getElem_cons (l:=List.finRange n) (i:=i) (by simpa using hi)]
  congr 1
  apply Fin.ext
  simp only [List.finRange,List.getElem_ofFn]

lemma scanFrom_fold {n : ℕ} (G : MatrixData n) (A S R : Vector Bool n) (i m : ℕ) (b : Best n) :
    scanFrom G A S R i m b =
      (((List.finRange n).drop i).take m).foldl (fun old v => step G A S R v old) b := by
  induction m generalizing i b with
  | zero => rfl
  | succ m ih =>
    by_cases hi : i<n
    · rw [scanFrom,dif_pos hi,finRange_drop hi,List.take_succ_cons,List.foldl_cons]
      exact ih (i+1) _
    · have hd : (List.finRange n).drop i = [] := List.drop_eq_nil_iff.mpr (by simp; omega)
      simp [scanFrom,hi,hd]

/-- The physically executed first-winner scan is exactly the mathematical
selector on the ordinary graph and the same three masks. -/
theorem choose_ofGraph {n : ℕ} (G : MatrixGraph n) (A S R : Vector Bool n) :
    choose (MatrixData.ofGraph G) A S R =
      UnitIntervalBitMasks.choose G.graph A.toList S.toList R.toList := by
  rw [choose,scanFrom_fold,List.drop_zero,List.take_of_length_le (by simp)]
  simp_rw [step_ofGraph]
  exact UnitIntervalBitMasks.choose_fold G.graph A.toList S.toList R.toList

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoice
