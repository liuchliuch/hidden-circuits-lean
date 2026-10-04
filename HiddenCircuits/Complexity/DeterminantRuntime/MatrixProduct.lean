import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProductCallback
import HiddenCircuits.Complexity.DeterminantRuntime.MatrixEntries

/-! Complete literal integer matrix multiplication with clean framing. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
open OracleBlock BinaryArithmetic Polynomial
open HiddenCircuits.Approximation.Initialization
variable {n : ℕ}

noncomputable def program : OracleBlock 24 := WordMatrixEmitter.arrayBlock cellProgram
noncomputable def timePolynomial : Polynomial ℕ :=
  X^2*(cellTime+10*(3*X+2)+24)+40*X+30

theorem executes (g : BitString → ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) :
    ∃ t, program.Executes g
      (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) [])
      (store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B))
        (encodeBitList (matrixWords (A*B)))) t ∧
      t ≤ timePolynomial.eval (inputSize A B) := by
  let p := params (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B))
  let N := inputSize A B
  have hc : ∀ g i j out inner outer, i<n → j<n → ∃ t,
      cellProgram.Executes g (MatrixEmitter.store n i j [] out inner outer p)
        (MatrixEmitter.store n i j (natEntry (A*B) i j) out inner outer p) t ∧ t ≤ cellTime.eval N := by
    intro g i j out inner outer hi hj
    simpa only [cellState_emitter, natEntry, dif_pos hi, dif_pos hj] using
      cell_executes g A B ⟨i,hi⟩ ⟨j,hj⟩ out inner outer
  have hw : ∀ i j, i<n → j<n → (natEntry (A*B) i j).length ≤ 3*N+2 := by
    intro i j hi hj
    simpa only [natEntry,dif_pos hi,dif_pos hj] using entry_length A B ⟨i,hi⟩ ⟨j,hj⟩
  obtain ⟨t,ht,hb⟩ := WordMatrixEmitter.arrayBlock_executes cellProgram (natEntry (A*B)) n
    (cellTime.eval N) (3*N+2) p hc hw g
  rw [emitter_matrixWords] at ht
  change program.Executes g _ _ t at ht
  dsimp only [p] at ht
  rw [emitter_output, ←store_emitter] at ht
  refine ⟨t,ht,hb.trans ?_⟩
  have hn : n ≤ N := by dsimp [N,inputSize];omega
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  change n*n*(cellTime.eval N+10*(3*N+2)+24)+40*n+30 ≤ _
  rw [pow_two]
  gcongr

theorem queryFree : program.QueryFree := WordMatrixEmitter.arrayBlock_queryFree _ cellProgram_queryFree

noncomputable def on {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) (g : BitString → ℕ)
    (A B : Matrix (Fin n) (Fin n) ℤ) (s : Store k)
    (hs : s ∘ φ = store n (encodeBitList (matrixWords A)) (encodeBitList (matrixWords B)) []) :
    ∃ t, (on φ).Executes g s (Function.update s (φ 7) (encodeBitList (matrixWords (A*B)))) t ∧
      t ≤ timePolynomial.eval (inputSize A B) := by
  obtain ⟨t,ht,hb⟩ := executes g A B
  refine ⟨t,?_,hb⟩
  apply rename_executes_to program φ g ht hs
  · have he : (Function.update s (φ 7) (encodeBitList (matrixWords (A*B)))) ∘ φ =
        Function.update (s ∘ φ) 7 (encodeBitList (matrixWords (A*B))) := by
      funext i; simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i; fin_cases i <;> rfl
  · intro i hi; exact Function.update_of_ne (hi 7).symm _ _

theorem on_queryFree {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ queryFree

end HiddenCircuits.Complexity.DeterminantRuntime.MatrixProduct
