import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentState
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionChoiceCorrect

/-! The fixed-clock physical component iteration refines the verified list-mask
scan. A stopped state stutters, so always-iterate and early-stop loops agree. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity DH.Runtime.PairCheck

def toLists {n : ℕ} (s : Data n) : UnitIntervalBitMasks.State n :=
  ⟨s.order,s.selected.toList,s.remaining.toList⟩

@[simp] lemma toLists_advance {n : ℕ} (s : Data n) (v : Fin n) :
    toLists (advance s v) =
      (⟨s.order++[v],UnitIntervalBitMasks.set s.selected.toList v true,
        UnitIntervalBitMasks.set s.remaining.toList v false⟩ : UnitIntervalBitMasks.State n) := by
  simp [toLists,advance,Vector.toList_set,UnitIntervalBitMasks.set]

lemma list_run_none {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) (s : Data n)
    (h : UnitIntervalBitMasks.choose G.graph A.toList s.selected.toList s.remaining.toList = none)
    (fuel : ℕ) : UnitIntervalBitMasks.run G.graph A.toList fuel (toLists s) = toLists s := by
  cases fuel <;> simp [UnitIntervalBitMasks.run,toLists,h]

lemma list_run_zero {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) (s : Data n) (v : Fin n)
    (h : UnitIntervalBitMasks.choose G.graph A.toList s.selected.toList s.remaining.toList = some v)
    (hz : UnitIntervalBitMasks.score G.graph s.selected.toList v = 0)
    (fuel : ℕ) : UnitIntervalBitMasks.run G.graph A.toList fuel (toLists s) = toLists s := by
  cases fuel <;> simp [UnitIntervalBitMasks.run,toLists,h,hz]

/-- Exact component-state refinement, for arbitrary masks and arbitrary initial
output lists. No geometric or runtime certificate is a premise. -/
theorem run_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) (fuel : ℕ) (s : Data n) :
    toLists (run (MatrixData.ofGraph G) A fuel s) =
      UnitIntervalBitMasks.run G.graph A.toList fuel (toLists s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [run,ih,UnitIntervalBitMasks.run]
    unfold step
    rw [UnitRecognitionChoice.choose_ofGraph]
    cases hc : UnitIntervalBitMasks.choose G.graph A.toList s.selected.toList s.remaining.toList with
    | none =>
      simp only [hc]
      simpa only [toLists,hc] using list_run_none G A s hc fuel
    | some v =>
      simp only [hc]
      rw [UnitRecognitionChoice.score_ofGraph]
      by_cases hz : UnitIntervalBitMasks.score G.graph s.selected.toList v = 0
      · simp only [hz,ite_true]
        simpa only [toLists,hc,hz,ite_true] using list_run_zero G A s v hc hz fuel
      · simp only [hz,ite_false,toLists,advance,Vector.toList_set,UnitIntervalBitMasks.set,hc]

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
