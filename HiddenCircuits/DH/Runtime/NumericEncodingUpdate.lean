import HiddenCircuits.DH.Runtime.StorageBounds
import HiddenCircuits.DH.Runtime.CoefficientRowModel

/-! Serialization equations for the literal three-array
numeric update, and the row-support facts derived from its genuine invariant. -/
namespace HiddenCircuits.DH.Runtime.NumericEncoding
open Complexity Complexity.BinaryArithmetic NumericStateModel PruningModel

lemma safe_support {n : ℕ} {s : NumericStateModel.State n} (h : Safe s) (v : Fin n) (k : ℕ)
    (hk:s.sizes[v.val]<k) : CoefficientModel.read s.rows[v.val] k=0:=by
  obtain ⟨bags,hr,_,_,_⟩:=h
  rw [hr.2.2 v k]
  exact BagExpr.state_zero_of_size_lt _ k (by rw [←hr.2.1 v];exact hk)
lemma update_table {n : ℕ} (s : NumericStateModel.State n) (a : Action n) :
    tableBits (update s a)=encodeBitList ((tableWords s).set a.keep.val
      (rowBits (CoefficientModel.mergeRow n a.kind s.sizes[a.keep.val] s.sizes[a.removed.val] s.rows[a.keep.val] s.rows[a.removed.val]))) := by
  simp [tableBits,tableWords,update,Vector.toList_set,List.map_set]
lemma update_sizes {n : ℕ} (s : NumericStateModel.State n) (a : Action n) :
    sizeBits (update s a)=encodeBitList ((sizeWords s).set a.keep.val
      (List.replicate (s.sizes[a.keep.val]+s.sizes[a.removed.val]) true)):=by
  simp [sizeBits,sizeWords,update,Vector.toList_set,List.map_set]
lemma update_live {n : ℕ} (s : NumericStateModel.State n) (a : Action n) :
    PairCheck.liveBits (update s a).alive=encodeBitList ((PairCheck.liveWords s.alive).set a.removed.val [false]):=by
  simp [PairCheck.liveBits,PairCheck.liveWords,update,remove,Vector.toList_set,List.map_set]
lemma runtime_row {n : ℕ} (s : NumericStateModel.State n) (h : Safe s) (a : Action n) :
    CoefficientRowRuntime.row n a.kind s.sizes[a.keep.val] s.sizes[a.removed.val] s.rows[a.keep.val] s.rows[a.removed.val]=
      CoefficientModel.mergeRow n a.kind s.sizes[a.keep.val] s.sizes[a.removed.val] s.rows[a.keep.val] s.rows[a.removed.val]:=
  CoefficientRowRuntime.row_eq_mergeRow _ _ _ _ _ _ (safe_support h a.keep) (safe_support h a.removed)
end HiddenCircuits.DH.Runtime.NumericEncoding
