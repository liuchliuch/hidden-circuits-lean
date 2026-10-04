import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointProgram
import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointCountValue

/-! The actual nested candidate/rank loops emit exactly the structural endpoint
encoding, for arbitrary record lists, without an external sorting certificate. -/
namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity BinaryArithmetic
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

 def emitRecord (R : List VertexRecord) (A : Accum) (x : VertexRecord) : Accum :=
  emitValues A (upperCount R x) (lowerCount R x)
 def rankSelected (R : List VertexRecord) (k : ℕ) (x : VertexRecord) : Bool :=
  !x.side && decide (leftRank R x=k)

lemma step_eq (R : List VertexRecord) (i k : ℕ) (A : Accum) :
    step R i k A=if rankSelected R k (R[i]?.getD defaultRecord) then
      emitRecord R A (R[i]?.getD defaultRecord) else A := by
  simp only [step,selected,rankSelected,emitRecord,countValue_leftRank,countValue_upperCount,countValue_lowerCount]

lemma range_map_getD {α : Type*} (xs : List α) (fallback : α) :
    (List.range xs.length).map (fun i=>xs[i]?.getD fallback)=xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
      Function.comp_def,List.getElem?_cons_zero,Option.getD_some,List.getElem?_cons_succ] using congrArg (List.cons a) ih

lemma runCandidates_fold (R : List VertexRecord) (k i m : ℕ) (A : Accum) :
    runCandidates R k i m A=(List.range' i m).foldl (fun A j=>step R j k A) A := by
  induction m generalizing i A with
  | zero => rfl
  | succ m ih =>
    rw [runCandidates,List.range'_succ,List.foldl_cons]
    exact ih _ _

lemma candidates_filter (R : List VertexRecord) (k : ℕ) (A : Accum) :
    runCandidates R k 0 R.length A=(R.filter (rankSelected R k)).foldl (emitRecord R) A := by
  rw [runCandidates_fold,←List.range_eq_range']
  simp only [step_eq]
  rw [←List.foldl_map (f := fun i=>R[i]?.getD defaultRecord)
    (g := fun A x=>if rankSelected R k x then emitRecord R A x else A),
    range_map_getD,←List.foldl_filter]

lemma runRanks_fold (R : List VertexRecord) (k m : ℕ) (A : Accum) :
    runRanks R k m A=(List.range' k m).foldl
      (fun A j=>(R.filter (rankSelected R j)).foldl (emitRecord R) A) A := by
  induction m generalizing k A with
  | zero => rfl
  | succ m ih =>
    rw [runRanks,List.range'_succ,List.foldl_cons,candidates_filter]
    exact ih _ _

lemma result_fold (R : List VertexRecord) :
    result R=(orderedLeft R).foldl (emitRecord R) initialAccum := by
  rw [result,runRanks_fold,←List.range_eq_range',←List.foldl_flatMap]
  rfl

lemma emitRecord_fold (R xs : List VertexRecord) (A : Accum) :
    xs.foldl (emitRecord R) A=
      ⟨(encodeBitList (xs.map (fun x=>List.replicate (lowValue R x) true))).reverse++A.lows,
       (encodeBitList (xs.map (fun x=>List.replicate (highValue R x) true))).reverse++A.highs,
       A.count+xs.length⟩ := by
  induction xs generalizing A with
  | nil => cases A; rfl
  | cons x xs ih =>
    rw [List.foldl_cons,ih]
    simp only [emitRecord,emitValues,List.map_cons,encodeBitList_eq_chunks,List.flatMap_cons,
      List.reverse_append,List.append_assoc,List.length_cons,lowValue,highValue,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- No oracle, annotation, or supplied ordering is used by the endpoint producer. -/
theorem computedBits_eq_bits (R : List VertexRecord) : computedBits R=bits R := by
  simp only [computedBits,result_fold,emitRecord_fold,initialAccum,List.append_nil,Nat.zero_add,
    List.reverse_reverse,bits]

end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
