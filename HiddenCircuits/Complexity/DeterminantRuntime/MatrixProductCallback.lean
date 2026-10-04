import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProductCell
import HiddenCircuits.Complexity.DeterminantRuntime.BitBounds

/-! A clean literal matrix-product entry callback with unconditional bounds. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
open OracleBlock BinaryArithmetic Polynomial
variable {n : ℕ}

noncomputable def cellProgram : OracleBlock 24 := seq rowSetup
  (seq gatherRow (seq columnSetup (seq gatherColumn (seq dotBlock cellCleanup))))

noncomputable def cellTime : Polynomial ℕ :=
  2*Gather.timePolynomial.comp (X^2+X+1)+dotAccumulatorTime.comp (4*X^2+1)+10*X^2+30*X+50

def inputSize (A B : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  n+(encodeBitList (matrixWords A)).length+(encodeBitList (matrixWords B)).length+1

theorem cell_executes (g : BitString → ℕ) (A B : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) (out inner outer : BitString) :
    ∃ t, cellProgram.Executes g
      (cellState n i.val j.val [] out inner outer (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) [] [] [] [])
      (cellState n i.val j.val (signedBits ((A*B) i j)) out inner outer
        (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) [] [] [] []) t ∧
      t ≤ cellTime.eval (inputSize A B) := by
  let a := encodeBitList (matrixWords A)
  let b := encodeBitList (matrixWords B)
  let N := inputSize A B
  obtain ⟨r,hr,hrb⟩ := gatherRow_executes g A i j (signedBits 0) out inner outer b
  obtain ⟨c,hc,hcb⟩ := gatherColumn_executes g B i j (signedBits 0) out inner outer a
    (List.replicate (i.val*n) true) (rowWords A i)
  obtain ⟨d,hd,hdb⟩ := dotBlock_executes g A B i j out inner outer a b
    (List.replicate (i.val*n) true) (List.replicate n true)
  have hs := rowSetup_executes g n i.val j.val out inner outer a b
  have hp := columnSetup_executes g n i.val j.val (signedBits 0) out inner outer a b
    (List.replicate (i.val*n) true) (rowWords A i)
  have hf := cellCleanup_executes g n i.val j.val (signedBits ((A*B) i j)) out inner outer a b
  have h := seq_executes _ _ g hs (seq_executes _ _ g hr (seq_executes _ _ g hp
    (seq_executes _ _ g hc (seq_executes _ _ g hd hf))))
  refine ⟨_,h,?_⟩
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  have ha : a.length ≤ N := by dsimp [N,inputSize,a];omega
  have hb : b.length ≤ N := by dsimp [N,inputSize,b];omega
  have hi : i.val ≤ N := i.isLt.le.trans hn
  have hj : j.val ≤ N := j.isLt.le.trans hn
  have hin : i.val*n ≤ N^2 := by simpa [pow_two] using Nat.mul_le_mul hi hn
  have hrg := Gather.timeBound_le_eval a.length (i.val*n) 1 n (N^2+N+1)
    (by omega) (by omega) (by omega) (by omega)
  have hcg := Gather.timeBound_le_eval b.length j.val n n (N^2+N+1)
    (by omega) (by omega) (by omega) (by omega)
  have hrlen := Gather.encoded_words_length (matrixWords A) (i.val*n) 1 n
  rw [gather_row] at hrlen
  have hclen := Gather.encoded_words_length (matrixWords B) j.val n n
  rw [gather_column] at hclen
  have hstream : 1+(rowWords A i).length+(columnWords B j).length ≤ 4*N^2+1 := by
    dsimp [rowWords,columnWords,N,inputSize,a,b] at *
    nlinarith
  have hdot := polynomial_nat_eval_mono dotAccumulatorTime hstream
  simp only [cellTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  change _ ≤ 2*Gather.timePolynomial.eval (N^2+N+1)+dotAccumulatorTime.eval (4*N^2+1)+10*N^2+30*N+50
  have hsetup : 5*i.val+(5*n+4)*i.val+11 ≤ 5*N+(5*N+4)*N+11 := by gcongr
  dsimp only [a,b] at hrg hcg
  dsimp only at hdot
  nlinarith

theorem entry_length (A B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (signedBits ((A*B) i j)).length ≤ 3*inputSize A B+2 := by
  let N := inputSize A B
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  have hA : EntriesBound A (2^N) := by
    intro i j
    apply abs_le_pow_signed_length
    apply (member_length_le_encodeBitList (entry_mem_matrixWords A i j)).trans
    dsimp [N,inputSize];omega
  have hB : EntriesBound B (2^N) := by
    intro i j
    apply abs_le_pow_signed_length
    apply (member_length_le_encodeBitList (entry_mem_matrixWords B i j)).trans
    dsimp [N,inputSize];omega
  have h := signedBits_length_of_abs_bound (product_abs_pow A B N N hn hA hB i j)
  convert h using 1 <;> omega

theorem cellProgram_queryFree : cellProgram.QueryFree := seq_queryFree _ _ rowSetup_queryFree
  (seq_queryFree _ _ gatherRow_queryFree (seq_queryFree _ _ columnSetup_queryFree
    (seq_queryFree _ _ gatherColumn_queryFree (seq_queryFree _ _ dotBlock_queryFree cellCleanup_queryFree))))

end HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
