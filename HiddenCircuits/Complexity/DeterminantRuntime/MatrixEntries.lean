import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProductLayout
import HiddenCircuits.Approximation.Initialization.WordMatrixEmitter

/-! Bridge between finite matrix indices and the literal row-major emitter. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open BinaryArithmetic
variable {n : ℕ}

def natEntry (A : Matrix (Fin n) (Fin n) ℤ) (i j : ℕ) : BitString :=
  if hi : i < n then if hj : j < n then signedBits (A ⟨i,hi⟩ ⟨j,hj⟩) else [] else []

theorem natEntry_fin (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    natEntry A i.val j.val = signedBits (A i j) := by simp [natEntry,i.isLt,j.isLt]

theorem range_map_eq_ofFn {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj; simp

theorem emitter_matrixWords (A : Matrix (Fin n) (Fin n) ℤ) :
    Approximation.Initialization.WordMatrixEmitter.matrixWords n (natEntry A) = matrixWords A := by
  unfold Approximation.Initialization.WordMatrixEmitter.matrixWords matrixWords
  change ((List.range n).map (fun i => (List.range n).map (natEntry A i))).flatten = _
  rw [range_map_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [range_map_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  exact natEntry_fin A i j

end HiddenCircuits.Complexity.DeterminantRuntime
