import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRounds
import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRootsCorrect

/-! End-to-end semantic correctness of the physical residual-only recognizer. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRounds
open Complexity DH.Runtime.PairCheck

lemma round_ofGraph {n : ℕ} (G : MatrixGraph n) (A : Vector Bool n) :
    (round (MatrixData.ofGraph G) A).toList = UnitIntervalComponentResidual.step G.graph A.toList :=
  UnitRecognitionRoots.residual_ofGraph G A

lemma run_ofGraph {n : ℕ} (G : MatrixGraph n) (fuel : ℕ) (A : Vector Bool n) :
    (run (MatrixData.ofGraph G) fuel A).toList = UnitIntervalComponentResidual.run G.graph fuel A.toList := by
  induction fuel generalizing A with
  | zero => rfl
  | succ fuel ih =>
    rw [run,ih,round_ofGraph]
    rfl

lemma count_vector {n : ℕ} (A : Vector Bool n) :
    UnitIntervalBitMasks.count (n:=n) A.toList = A.toList.countP id := by
  have hmap : (List.finRange n).map (fun v => A[v.val]) = A.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [List.finRange]
  calc
    UnitIntervalBitMasks.count (n:=n) A.toList = (List.finRange n).countP (fun v => A[v.val]) := by
      apply List.countP_congr
      intro v _
      rw [UnitRecognitionChoice.read_vector]
    _ = ((List.finRange n).map (fun v => A[v.val])).countP id := by
      rw [List.countP_map]
      rfl
    _ = _ := by rw [hmap]

lemma all_not_iff_count {n : ℕ} (A : Vector Bool n) :
    A.toList.all Bool.not = true ↔ UnitIntervalBitMasks.count (n:=n) A.toList = 0 := by
  rw [count_vector,List.all_eq_true,List.countP_eq_zero]
  apply forall_congr'
  intro b
  apply forall_congr'
  intro _
  cases b <;> simp

/-- The concrete program's acceptance predicate is exactly the natural real
unit-interval graph class. No order, representation, or certificate is supplied. -/
theorem accepts_ofGraph_iff {n : ℕ} (G : MatrixGraph n) :
    accepts (MatrixData.ofGraph G) = true ↔ RealUnitInterval.UnitIntervalGraph G.graph := by
  rw [accepts,all_not_iff_count,run_ofGraph]
  simp only [Vector.toList_replicate]
  exact UnitIntervalComponentResidual.accepts_iff G.graph

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionRounds
