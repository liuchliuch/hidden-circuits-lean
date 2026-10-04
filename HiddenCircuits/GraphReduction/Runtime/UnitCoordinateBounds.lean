import HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRow

/-! Linear signed-sum envelopes close every intermediate register
bound, without assuming a coordinate certificate or a pre-bounded execution. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRow
open Complexity Complexity.BinaryArithmetic RegisterMachine

noncomputable def resultBound (width height n : ℕ) (x : VertexRecord) : ℕ :=
  SignedCounter.counterBound (SignedCounter.counterBound (registerBound width height x) n) n

lemma correction_sum_abs (second : Bool) (width : ℕ) (x : VertexRecord) (records : List VertexRecord) :
    ((records.map (unitCorrectionValue second width x)).sum).natAbs≤records.length := by
  induction records with
  | nil => simp
  | cons y ys ih =>
    have hy : (unitCorrectionValue second width x y).natAbs≤1 := by
      rcases unitCorrectionValue_cases second width x y with h|h|h <;> rw [h] <;> norm_num
    simpa only [List.map_cons,List.sum_cons,List.length_cons] using
      (Int.natAbs_add_le (unitCorrectionValue second width x y) ((ys.map (unitCorrectionValue second width x)).sum)).trans
        (show (unitCorrectionValue second width x y).natAbs+((ys.map (unitCorrectionValue second width x)).sum).natAbs≤ys.length+1 by omega)

theorem result_bounded (width height : ℕ) (records : List VertexRecord) (x : VertexRecord) :
    Bounded (resultBound width height records.length x) (result width height records x) := by
  let R:=UnitBaselineRow.registers width height x
  let C:=registerBound width height x
  have hR : Bounded C R:=UnitBaseline.result_bounded width height x
  have hv:=UnitBaseline.result_value width height x
  change R 2=_ at hv
  cases hp:x.probe with
  | false =>
    let a:=(records.map (unitCorrectionValue false width x)).sum
    let b:=(records.map (unitCorrectionValue true width x)).sum
    have h1:=SignedCounter.bounded_counter R C records.length a hR (correction_sum_abs false width x records)
    have h2:=SignedCounter.bounded_counter (Function.update R 2 (R 2+a))
      (SignedCounter.counterBound C records.length) records.length b h1 (correction_sum_abs true width x records)
    have he : Function.update (Function.update R 2 (R 2+a)) 2
        ((Function.update R 2 (R 2+a)) 2+b)=result width height records x := by
      simp only [Function.update_self,Function.update_idem,result]
      congr 1
      simp only [unitCoordinate,hp,Bool.false_eq_true,ite_false] at hv ⊢
      rw [hv]
    rw [he] at h2
    exact h2
  | true =>
    have he : result width height records x=R := by
      unfold result
      change Function.update R 2 (unitCoordinate width height records x)=R
      simp only [unitCoordinate,hp,ite_true] at hv ⊢
      rw [←hv,Function.update_eq_self]
    rw [he]
    exact hR.mono (by unfold C resultBound SignedCounter.counterBound;omega)
end HiddenCircuits.GraphReduction.Runtime.UnitCoordinateRow
