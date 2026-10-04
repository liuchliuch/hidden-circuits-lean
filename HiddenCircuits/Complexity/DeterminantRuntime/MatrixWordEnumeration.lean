import HiddenCircuits.Complexity.DeterminantRuntime.Encoding
import HiddenCircuits.Approximation.Initialization.WordMatrixEmitter

namespace HiddenCircuits.Complexity.DeterminantRuntime
open Approximation.Initialization
lemma map_fin_val (n : ℕ) {α : Type*} (f : ℕ → α) :
    (List.finRange n).map (fun i => f i.val)=(List.range n).map f := by
  rw [←List.map_coe_finRange_eq_range (n := n),List.map_map]
  rfl
lemma emitter_matrixWords_of_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (entry : ℕ → ℕ → BitString)
    (h : ∀i j : Fin n,entry i.val j.val=BinaryArithmetic.signedBits (A i j)) :
    WordMatrixEmitter.matrixWords n entry=matrixWords A := by
  simp only [WordMatrixEmitter.matrixWords,List.flatMap_def,matrixWords,List.ofFn_eq_map]
  simp_rw [←map_fin_val]
  apply congrArg List.flatten
  apply congrArg (fun f => (List.finRange n).map f)
  funext i
  apply congrArg (fun f => (List.finRange n).map f)
  funext j
  exact h i j
end HiddenCircuits.Complexity.DeterminantRuntime
