import HiddenCircuits.DH.Runtime.PairSearchModel
import HiddenCircuits.DH.Runtime.SearchOrder

/-! The exact guarded unary-index search order is row-major first success. -/
namespace HiddenCircuits.DH.Runtime.PairSearch
open Complexity PairCheck

lemma finRange_drop {n j : ℕ} (hj : j<n) :
    (List.finRange n).drop j=⟨j,hj⟩::(List.finRange n).drop (j+1) := by
  rw [List.drop_eq_getElem_cons (l:=List.finRange n) (i:=j) (by simpa using hj)]
  congr 1
  apply Fin.ext
  simp only [List.finRange,List.getElem_ofFn]

lemma rowFrom_fold {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (u : Fin n)
    (j m : ℕ) (found : Option (PruningModel.Action n)) :
    rowFrom G alive u j m found =
      (((List.finRange n).drop j).take m).foldl (fun old v=>step G alive u v old) found := by
  induction m generalizing j found with
  | zero => rfl
  | succ m ih =>
    by_cases hj : j<n
    · rw [rowFrom,dif_pos hj,finRange_drop hj,List.take_succ_cons,List.foldl_cons]
      exact ih (j+1) _
    · have hd : (List.finRange n).drop j=[] := List.drop_eq_nil_iff.mpr (by simp;omega)
      simp [rowFrom,hj,hd]

lemma rowsFrom_fold {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) (i m : ℕ)
    (found : Option (PruningModel.Action n)) :
    rowsFrom G alive i m found =
      (((List.finRange n).drop i).take m).foldl (fun old u=>
        (List.finRange n).foldl (fun out v=>step G alive u v out) old) found := by
  induction m generalizing i found with
  | zero => rfl
  | succ m ih =>
    by_cases hi : i<n
    · rw [rowsFrom,dif_pos hi,finRange_drop hi,List.take_succ_cons,List.foldl_cons,ih,rowFrom_fold]
      have ht : (List.finRange n).take n=List.finRange n := List.take_of_length_le (by simp)
      simp only [List.drop_zero,ht]
    · have hd : (List.finRange n).drop i=[] := List.drop_eq_nil_iff.mpr (by simp;omega)
      simp [rowsFrom,hi,hd]

lemma find_first {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) :
    find G alive=SearchOrder.first (fun uv=>tryPair G alive uv.1 uv.2) (PruningModel.candidates n) := by
  have ht : (List.finRange n).take n=List.finRange n := List.take_of_length_le (by simp)
  rw [find,rowsFrom_fold,List.drop_zero,ht]
  simp only [step]
  rw [SearchOrder.nested_first]
  rfl

/-- The raw literal machine search specializes to precisely the already
verified ordinary-graph pruning scan, including pendant-first pair selection. -/
theorem find_ofGraph {n : ℕ} (G : MatrixGraph n) (alive : Vector Bool n) :
    find (MatrixData.ofGraph G) alive=PruningModel.find G.graph alive := by
  rw [find_first]
  simp_rw [tryPair_ofGraph]
  exact (SearchOrder.scan_eq_first G.graph alive _).symm

/-- Every raw search result retains the distinct-live endpoint invariant,
even when its Boolean matrix is not the adjacency matrix of a simple graph. -/
theorem find_live {n : ℕ} (G : MatrixData n) (alive : Vector Bool n) {a : PruningModel.Action n}
    (h : find G alive=some a) :
    alive[a.keep.val]=true ∧ alive[a.removed.val]=true ∧ a.keep≠a.removed := by
  rw [find_first] at h
  obtain ⟨uv,huv,he⟩ := SearchOrder.first_some _ _ h
  exact tryPair_live G alive uv.1 uv.2 he

end HiddenCircuits.DH.Runtime.PairSearch
