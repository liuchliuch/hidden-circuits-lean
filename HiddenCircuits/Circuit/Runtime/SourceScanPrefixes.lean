import HiddenCircuits.Circuit.Runtime.SourceScanSemantics
import HiddenCircuits.Complexity.GridPrefixStates

/-! Exact row-major prefixes for source gate emission and scalar accounting. -/
namespace HiddenCircuits.Circuit.Runtime
open HiddenCircuits.Complexity

lemma gridFinIndices_eq_sourcePairs (k : ℕ) : gridFinIndices k k=sourcePairs (k+1) := by
  unfold gridFinIndices sourcePairs
  rw [List.ofFn_mul,List.flatMap_def,←List.ofFn_eq_map]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [←List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*(k+1)+j.val,by have hi:=i.isLt;have hj:=j.isLt;nlinarith⟩ : Fin ((k+1)*(k+1)))=
      finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [he]
  exact finProdFinEquiv.symm_apply_apply _

def scanGates {k : ℕ} (G : MatrixGraph (k+1)) (i j : ℕ) : List (ConstraintGate (k+1)) :=
  (gridPrefix k k i j).flatMap (fun p => edgeGates G p.1 p.2)

def scanSwaps {k : ℕ} (G : MatrixGraph (k+1)) (i j : ℕ) : ℕ :=
  ((gridPrefix k k i j).map (fun p => edgeSwapPairs G p.1 p.2)).sum

@[simp] lemma scanGates_zero {k : ℕ} (G : MatrixGraph (k+1)) : scanGates G 0 0=[] := by simp [scanGates]
@[simp] lemma scanSwaps_zero {k : ℕ} (G : MatrixGraph (k+1)) : scanSwaps G 0 0=0 := by simp [scanSwaps]

lemma scanGates_succ {k : ℕ} (G : MatrixGraph (k+1)) (i j : Fin (k+1)) :
    scanGates G i.val (j.val+1)=scanGates G i.val j.val++edgeGates G i j := by
  simp [scanGates,gridPrefix_succ]
lemma scanSwaps_succ {k : ℕ} (G : MatrixGraph (k+1)) (i j : Fin (k+1)) :
    scanSwaps G i.val (j.val+1)=scanSwaps G i.val j.val+edgeSwapPairs G i j := by
  simp [scanSwaps,gridPrefix_succ,List.sum_append]
lemma scanGates_row {k : ℕ} (G : MatrixGraph (k+1)) (i : ℕ) :
    scanGates G i (k+1)=scanGates G (i+1) 0 := by rw [scanGates,scanGates,gridPrefix_row]
lemma scanSwaps_row {k : ℕ} (G : MatrixGraph (k+1)) (i : ℕ) :
    scanSwaps G i (k+1)=scanSwaps G (i+1) 0 := by rw [scanSwaps,scanSwaps,gridPrefix_row]

lemma scanGates_final {k : ℕ} (G : MatrixGraph (k+1)) :
    scanGates G (k+1) 0=(restoringEdges (sourceEdges G)).gates := by
  rw [scanGates,gridPrefix_final,gridFinIndices_eq_sourcePairs,sourceScan_gates]

lemma scanSwaps_final {k : ℕ} (G : MatrixGraph (k+1)) :
    scanSwaps G (k+1) 0=restoringSwapPairs (sourceEdges G) := by
  rw [scanSwaps,gridPrefix_final,gridFinIndices_eq_sourcePairs,sourceScan_swaps]

end HiddenCircuits.Circuit.Runtime
