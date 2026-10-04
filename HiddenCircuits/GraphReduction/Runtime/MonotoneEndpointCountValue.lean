import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointState

/-! Literal index scans count exactly the selected record predicates. -/
namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime

lemma filter_range_getD_length {α : Type*} (xs : List α) (fallback : α) (f : α→Bool) :
    ((List.range xs.length).filter (fun i => f (xs[i]?.getD fallback))).length=(xs.filter f).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons,List.range_succ_eq_map,List.filter_cons,List.filter_map,List.length_map,
      Function.comp_def,List.getElem?_cons_zero,Option.getD_some,List.getElem?_cons_succ]
    cases ha:f a <;> simp [ha,ih]

lemma countValue_filter (lower right : Bool) (R : List VertexRecord) (i : ℕ) :
    countValue lower right R i=(R.filter (fun y =>
      MonotoneOrderRuntime.outputValue lower right false y (R[i]?.getD defaultRecord))).length := by
  rw [countValue,UnaryCount.rowCount_eq,←List.range_eq_range']
  simpa only [edge, MonotoneOrderRuntime.recordLT] using
    filter_range_getD_length R defaultRecord
      (fun y => MonotoneOrderRuntime.outputValue lower right false y (R[i]?.getD defaultRecord))
lemma countValue_leftRank (R : List VertexRecord) (i : ℕ) :
    countValue false false R i=leftRank R (R[i]?.getD defaultRecord) := by
  rw [countValue_filter]
  rfl
lemma countValue_upperCount (R : List VertexRecord) (i : ℕ) :
    countValue false true R i=upperCount R (R[i]?.getD defaultRecord) := by
  rw [countValue_filter]
  rfl
lemma countValue_lowerCount (R : List VertexRecord) (i : ℕ) :
    countValue true true R i=lowerCount R (R[i]?.getD defaultRecord) := by
  rw [countValue_filter]
  rfl
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
