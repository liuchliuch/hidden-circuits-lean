import HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonalCell
import HiddenCircuits.Complexity.DeterminantRuntime.GatherSemantics
import HiddenCircuits.Complexity.DeterminantRuntime.MatrixEntries
import HiddenCircuits.Complexity.BinaryArithmetic.StraightLine

/-! Fresh reconstruction: the concrete diagonal-entry callback and input-derived bounds. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
open OracleBlock BinaryArithmetic Polynomial MatrixProduct
variable {n : ℕ}

noncomputable def cellTime : Polynomial ℕ := 1000*(X+1)^4+40*X+operationTime.comp (2*X)+40
def inputSize (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) : ℕ :=
  n+(encodeBitList (matrixWords A)).length+(signedBits c).length+1

theorem readBound_le (n i j L N : ℕ) (hn : n ≤ N) (hi : i ≤ N) (hj : j ≤ N) (hL : L ≤ N) :
    readBound n i j L ≤ 1000*(N+1)^4 := by
  have hidx : i*n+j ≤ N^2+N := by have hh := Nat.mul_le_mul hi hn;nlinarith
  unfold readBound GraphReduction.Runtime.lookupBound
  calc
    _ ≤ 5*N+(5*N+4)*N+5*N+(5*N+5*(N^2+N)+((N^2+N)+1)*(6*N+14)+9)+(N^2+N)+14 := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3),Nat.zero_le (N^4)]

lemma entry_bound (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (i j : Fin n) :
    (signedBits (A i j)).length ≤ inputSize A c := by
  apply (member_length_le_encodeBitList (entry_mem_matrixWords A i j)).trans
  unfold inputSize;omega
lemma scalar_entry (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (i j : Fin n) :
    (A+Matrix.scalar (Fin n) c) i j=(if i.val=j.val then A i j+c else A i j) := by
  change A i j + (Matrix.diagonal (fun _ : Fin n => c)) i j = _
  by_cases h : i.val=j.val <;> simp [Matrix.diagonal_apply,Fin.ext_iff,h]

lemma cell_executes (g : BitString → ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ)
    (i j : Fin n) (out inner outer : BitString) :
    ∃t,cell.Executes g (base n i.val j.val [] out inner outer (encodeBitList (matrixWords A)) (signedBits c))
      (base n i.val j.val (signedBits ((A+Matrix.scalar (Fin n) c) i j)) out inner outer
        (encodeBitList (matrixWords A)) (signedBits c)) t ∧ t ≤ cellTime.eval (inputSize A c) := by
  obtain ⟨a,ha,hab⟩ := readCell_executes g n i.val j.val (matrixWords A) (signedBits c) out inner outer
  rw [matrixWords_get] at ha
  obtain ⟨b,hb,hbb⟩ := modifyCell_executes g n i.val j.val out inner outer
    (encodeBitList (matrixWords A)) (A i j) c
  rw [←scalar_entry A c i j] at hb
  refine ⟨a+b+2,seq_executes _ _ g ha hb,?_⟩
  let N := inputSize A c
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  have hi : i.val ≤ N := i.isLt.le.trans hn
  have hj : j.val ≤ N := j.isLt.le.trans hn
  have hL : (encodeBitList (matrixWords A)).length ≤ N := by dsimp [N,inputSize];omega
  have hc : (signedBits c).length ≤ N := by dsimp [N,inputSize];omega
  have hx := entry_bound A c i j
  have hr := readBound_le n i.val j.val (encodeBitList (matrixWords A)).length N hn hi hj hL
  have hp := polynomial_nat_eval_mono operationTime (show (signedBits (A i j)).length+(signedBits c).length ≤ 2*N by dsimp [N];omega)
  dsimp only at hp
  simp only [cellTime,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat,eval_comp]
  change _ ≤ 1000*(N+1)^4+40*N+operationTime.eval (2*N)+40
  omega

lemma entry_length (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (i j : Fin n) :
    (signedBits ((A+Matrix.scalar (Fin n) c) i j)).length ≤ 2*inputSize A c+3 := by
  have hx := entry_bound A c i j
  have hc : (signedBits c).length ≤ inputSize A c := by unfold inputSize;omega
  rw [scalar_entry]
  by_cases h:i.val=j.val
  · rw [if_pos h]
    exact RegisterMachine.operation_bitLength Operation.add (A i j) c _ hx hc
  · rw [if_neg h]
    omega
end HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
