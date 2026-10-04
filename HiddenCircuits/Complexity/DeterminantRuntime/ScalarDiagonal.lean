import HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonalCallback

/-! Complete literal scalar-diagonal addition, with clean 25-port framing. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
open OracleBlock BinaryArithmetic Polynomial Approximation.Initialization
variable {n : ℕ}

noncomputable def matrixProgram : OracleBlock 24 := WordMatrixEmitter.arrayBlock cell
noncomputable def time : Polynomial ℕ := X^2*(cellTime+10*(2*X+3)+24)+40*X+30

theorem executes (g : BitString → ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) :
    ∃ t, matrixProgram.Executes g (MatrixProduct.store n (encodeBitList (matrixWords A)) (signedBits c) [])
      (MatrixProduct.store n (encodeBitList (matrixWords A)) (signedBits c)
        (encodeBitList (matrixWords (A+Matrix.scalar (Fin n) c)))) t ∧
      t ≤ time.eval (inputSize A c) := by
  let p := MatrixProduct.params (encodeBitList (matrixWords A)) (signedBits c)
  let N := inputSize A c
  have hc : ∀ g i j out inner outer, i<n → j<n → ∃ t,
      cell.Executes g (MatrixEmitter.store n i j [] out inner outer p)
        (MatrixEmitter.store n i j (natEntry (A+Matrix.scalar (Fin n) c) i j) out inner outer p) t ∧
          t ≤ cellTime.eval N := by
    intro g i j out inner outer hi hj
    simpa only [base,MatrixProduct.cellState_emitter,natEntry,dif_pos hi,dif_pos hj] using
      cell_executes g A c ⟨i,hi⟩ ⟨j,hj⟩ out inner outer
  have hw : ∀ i j, i<n → j<n → (natEntry (A+Matrix.scalar (Fin n) c) i j).length ≤ 2*N+3 := by
    intro i j hi hj
    simpa only [natEntry,dif_pos hi,dif_pos hj] using entry_length A c ⟨i,hi⟩ ⟨j,hj⟩
  obtain ⟨t,ht,hb⟩ := WordMatrixEmitter.arrayBlock_executes cell (natEntry (A+Matrix.scalar (Fin n) c)) n
    (cellTime.eval N) (2*N+3) p hc hw g
  rw [emitter_matrixWords] at ht
  change matrixProgram.Executes g _ _ t at ht
  dsimp only [p] at ht
  rw [MatrixProduct.emitter_output,←MatrixProduct.store_emitter] at ht
  refine ⟨t,ht,hb.trans ?_⟩
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  change n*n*(cellTime.eval N+10*(2*N+3)+24)+40*n+30 ≤ _
  rw [pow_two]
  gcongr

theorem matrixProgram_queryFree : matrixProgram.QueryFree := WordMatrixEmitter.arrayBlock_queryFree _ cell_queryFree

noncomputable def on {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : OracleBlock k := rename matrixProgram φ

theorem on_executes {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) (g : BitString → ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (c : ℤ) (s : Store k)
    (hs : s ∘ φ = MatrixProduct.store n (encodeBitList (matrixWords A)) (signedBits c) []) :
    ∃ t, (on φ).Executes g s
      (Function.update s (φ 7) (encodeBitList (matrixWords (A+Matrix.scalar (Fin n) c)))) t ∧
      t ≤ time.eval (inputSize A c) := by
  obtain ⟨t,ht,hb⟩ := executes g A c
  refine ⟨t,?_,hb⟩
  apply rename_executes_to matrixProgram φ g ht hs
  · have he : (Function.update s (φ 7) (encodeBitList (matrixWords (A+Matrix.scalar (Fin n) c)))) ∘ φ =
        Function.update (s ∘ φ) 7 (encodeBitList (matrixWords (A+Matrix.scalar (Fin n) c))) := by
      funext q; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext q; fin_cases q <;> rfl
  · intro q hq;exact Function.update_of_ne (hq 7).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : (on φ).QueryFree :=
  rename_queryFree _ _ matrixProgram_queryFree

end HiddenCircuits.Complexity.DeterminantRuntime.ScalarDiagonal
