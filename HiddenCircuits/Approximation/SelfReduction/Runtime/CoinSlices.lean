import HiddenCircuits.Approximation.SelfReduction.CoinExperiment
import HiddenCircuits.Approximation.SelfReduction.Runtime.StatisticalBridge
import Mathlib.Data.List.OfFn

/-! Exact byte ordering of the product-space random experiment. These equalities
connect the physical prefix-pop loops to the finite independent coordinates. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open Complexity

 theorem splitBlocks_apply (n m : ℕ) (r : CoinTape (n*m)) (i : Fin n) (j : Fin m) :
    splitBlocks n m r i j=r (finProdFinEquiv (i,j)) := rfl

 theorem ofFn_splitBlocks (n m : ℕ) (r : CoinTape (n*m)) :
    (List.ofFn (fun i => List.ofFn (splitBlocks n m r i))).flatten=List.ofFn r := by
  rw [List.ofFn_mul r]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [splitBlocks_apply]
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

 theorem ofFn_cast {n m : ℕ} (h : n=m) {α : Type*} (f : Fin m → α) :
    List.ofFn (fun i => f (Fin.cast h i))=List.ofFn f := by
  subst m
  rfl

 theorem ofFn_splitBlocks_two (q M m : ℕ) (r : CoinTape (q*(M*m))) :
    (List.ofFn (fun i => List.ofFn (fun j =>
      List.ofFn (splitBlocks M m (splitBlocks q (M*m) r i) j)))).flatten.flatten=List.ofFn r := by
  have he (xs : List (List (List Bool))) : xs.flatten.flatten=(xs.map List.flatten).flatten := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.flatten_cons,List.map_cons,List.flatten_append,ih]
  rw [he,List.map_ofFn]
  simp only [Function.comp_def,ofFn_splitBlocks]

/-- Physical per-confidence-group coin strings, with the harmless arithmetic
cast between `2*k+2` and `2*(k+1)` made explicit once. -/
def stageCoinBlocks (m T k : ℕ) (r : StageTape (CoinTape m) T k) :
    Fin (2*k+1+1) → List BitString :=
  fun i => List.ofFn (fun j => List.ofFn (r (Fin.cast (repeatCount_eq k) i) j))

@[simp] theorem stageCoinBlocks_length (m T k : ℕ) (r : StageTape (CoinTape m) T k)
    (i : Fin (2*k+1+1)) : (stageCoinBlocks m T k r i).length=batchSize T := by simp [stageCoinBlocks]

 theorem stageCoinBlocks_width (m T k : ℕ) (r : StageTape (CoinTape m) T k)
    (i : Fin (2*k+1+1)) (bits : BitString) (h : bits∈stageCoinBlocks m T k r i) : bits.length=m := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  simp

 theorem stageCoinBlocks_flatten (m T k : ℕ) (r : CoinTape (2*(k+1)*(batchSize T*m))) :
    (List.ofFn (stageCoinBlocks m T k
      (fun i => splitBlocks (batchSize T) m (splitBlocks (2*(k+1)) (batchSize T*m) r i)))).flatten.flatten=
      List.ofFn r := by
  have hc := ofFn_cast (repeatCount_eq k) (fun i : Fin (2*(k+1)) =>
    List.ofFn (fun j => List.ofFn (splitBlocks (batchSize T) m (splitBlocks (2*(k+1)) (batchSize T*m) r i) j)))
  change (List.ofFn (fun i => List.ofFn (fun j => List.ofFn (splitBlocks (batchSize T) m
    (splitBlocks (2*(k+1)) (batchSize T*m) r (Fin.cast (repeatCount_eq k) i)) j)))).flatten.flatten=List.ofFn r
  rw [hc]
  exact ofFn_splitBlocks_two _ _ _ r

end HiddenCircuits.Approximation.SelfReduction.Runtime
