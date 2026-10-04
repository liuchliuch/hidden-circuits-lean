import HiddenCircuits.GraphReduction.Runtime.UnitSignedScan

/-! The actual bounded scan sums exactly the descriptor correction
list already identified with the paper's signed prefix displacement. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitSignedScan
open Complexity

lemma total_sum (edge : ℕ → ℕ → Bool × Bool) (i j m : ℕ) :
    SignedScan.total edge i j m=∑k : Fin m,SignedCounter.value (edge i (j+k.val)) := by
  induction m generalizing j with
  | zero => simp [SignedScan.total]
  | succ m ih =>
    rw [SignedScan.total,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 2
    omega

lemma flag_value (second : Bool) (width : ℕ) (x y : VertexRecord) :
    SignedCounter.value (decide (unitCorrectionValue second width x y=1),
      decide (unitCorrectionValue second width x y=-1))=unitCorrectionValue second width x y := by
  rcases unitCorrectionValue_cases second width x y with h|h|h <;> simp [h,SignedCounter.value]

 theorem total_correct (second : Bool) (width : ℕ) (records : List VertexRecord) (i : Fin records.length) :
    SignedScan.total (edge second width records) i.val 0 records.length=
      (records.map (unitCorrectionValue second width (records.get i))).sum := by
  rw [total_sum]
  simp only [Nat.zero_add]
  have h : ∀j : Fin records.length,
      SignedCounter.value (edge second width records i.val j.val)=
        unitCorrectionValue second width (records.get i) (records.get j) := by
    intro j
    unfold edge
    simp only [List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem j.isLt,Option.getD_some]
    exact flag_value second width _ _
  simp_rw [h]
  rw [←List.sum_ofFn]
  congr 1
  change List.ofFn ((unitCorrectionValue second width (records.get i)) ∘ records.get)=_
  rw [←List.map_ofFn,List.ofFn_get]
end HiddenCircuits.GraphReduction.Runtime.UnitSignedScan
