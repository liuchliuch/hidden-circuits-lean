import HiddenCircuits.Complexity.DeterminantRuntime.BitBounds
import HiddenCircuits.Complexity.DeterminantRuntime.MatrixEntries

/-! Unconditional polynomial storage envelope for every determinant round. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open BinaryArithmetic
variable {n : ℕ}

theorem matrix_array_length_bound (A : Matrix (Fin n) (Fin n) ℤ) (W : ℕ)
    (hW : ∀ i j, (signedBits (A i j)).length ≤ W) :
    (encodeBitList (matrixWords A)).length ≤ n*n*(2*W+2) := by
  rw [← matrixWords_length A]
  apply Approximation.Initialization.WordMatrixEmitter.encode_length_bound
  intro w hw
  obtain ⟨row,hrow,hw⟩ := List.mem_flatten.mp hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
  exact hW i j

theorem prefix_product_bitLength (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    ∀ i j, (signedBits ((A*(faddeevState A k).1) i j)).length ≤ 4*((matrixInput A).length+1)^2 := by
  let L := (matrixInput A).length
  have hn := dimension_le_input A
  have hp := product_abs_pow A (faddeevState A k).1 L (4*(L+1)*k) hn
    (entry_abs_le_input_pow A) (faddeevState_input_abs A k).1
  intro i j
  apply (signedBits_length_of_abs_bound (hp i j)).trans
  dsimp [L] at *
  nlinarith

theorem prefix_trace_bitLength (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    (signedBits (A*(faddeevState A k).1).trace).length ≤ 4*((matrixInput A).length+1)^2 := by
  let L := (matrixInput A).length
  have hn := dimension_le_input A
  have hp := product_abs_pow A (faddeevState A k).1 L (4*(L+1)*k) hn
    (entry_abs_le_input_pow A) (faddeevState_input_abs A k).1
  have ht := trace_abs_pow (A*(faddeevState A k).1) L (2*L+4*(L+1)*k) hn hp
  apply (signedBits_length_of_abs_bound ht).trans
  dsimp [L] at *
  nlinarith

def roundSizeBound (A : Matrix (Fin n) (Fin n) ℤ) : ℕ := 100*((matrixInput A).length+1)^4

theorem input_le_roundSizeBound (A : Matrix (Fin n) (Fin n) ℤ) :
    (matrixInput A).length ≤ roundSizeBound A := by
  let L := (matrixInput A).length
  have h1 : L+1 ≤ (L+1)^4 := Nat.le_self_pow (by decide : 4 ≠ 0) (L+1)
  unfold roundSizeBound
  change L ≤ 100*(L+1)^4
  omega

theorem word_le_roundSizeBound (A : Matrix (Fin n) (Fin n) ℤ) :
    4*((matrixInput A).length+1)^2 ≤ roundSizeBound A := by
  let N := (matrixInput A).length+1
  have h1 : N^2 ≤ (N^2)^2 := Nat.le_self_pow (by decide : 2 ≠ 0) (N^2)
  unfold roundSizeBound
  change 4*N^2 ≤ 100*N^4
  nlinarith [show (N^2)^2=N^4 by ring]

theorem bounded_array_le_roundSizeBound (A C : Matrix (Fin n) (Fin n) ℤ)
    (hC : ∀ i j, (signedBits (C i j)).length ≤ 4*((matrixInput A).length+1)^2) :
    (encodeBitList (matrixWords C)).length ≤ roundSizeBound A := by
  have h := matrix_array_length_bound C _ hC
  have hn := dimension_le_input A
  let N := (matrixInput A).length+1
  have hnn : n*n ≤ N^2 := by dsimp [N];nlinarith
  have hp : 1 ≤ N^2 := Nat.one_le_pow _ _ (by dsimp [N];omega)
  have hmul := Nat.mul_le_mul_right (2*(4*N^2)+2) hnn
  unfold roundSizeBound
  change _ ≤ 100*N^4
  change _ ≤ n*n*(2*(4*N^2)+2) at h
  nlinarith [show N^2*N^2=N^4 by ring]

theorem prefix_round_bounds (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    n ≤ roundSizeBound A ∧ k ≤ roundSizeBound A ∧
    (encodeBitList (matrixWords A)).length ≤ roundSizeBound A ∧
    (encodeBitList (matrixWords (faddeevState A k).1)).length ≤ roundSizeBound A ∧
    (signedBits (faddeevState A k).2).length ≤ roundSizeBound A ∧
    (encodeBitList (matrixWords (A*(faddeevState A k).1))).length ≤ roundSizeBound A ∧
    (signedBits (A*(faddeevState A k).1).trace).length ≤ roundSizeBound A ∧
    (signedBits (faddeevState A (k+1)).2).length ≤ roundSizeBound A ∧
    (encodeBitList (matrixWords (faddeevState A (k+1)).1)).length ≤ roundSizeBound A := by
  have hn := (dimension_le_input A).trans (input_le_roundSizeBound A)
  have hB := faddeevState_bitLength A k hk.le
  have hnext := faddeevState_bitLength A (k+1) hk
  exact ⟨hn,hk.le.trans hn,(array_length_le_input A).trans (input_le_roundSizeBound A),
    bounded_array_le_roundSizeBound A _ hB.1,hB.2.trans (word_le_roundSizeBound A),
    bounded_array_le_roundSizeBound A _ (prefix_product_bitLength A k hk),
    (prefix_trace_bitLength A k hk).trans (word_le_roundSizeBound A),
    hnext.2.trans (word_le_roundSizeBound A),bounded_array_le_roundSizeBound A _ hnext.1⟩

end HiddenCircuits.Complexity.DeterminantRuntime
