import HiddenCircuits.Complexity.DeterminantRuntime.MatrixProductLayout
import HiddenCircuits.Complexity.DeterminantRuntime.MatrixWordEnumeration
import HiddenCircuits.Complexity.GraphVerifier.ReadOnlyLength

/-! Fresh reconstruction of the actual25-stack identity-matrix word emitter. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.IdentityMatrix
open OracleBlock BinaryArithmetic Polynomial Approximation.Initialization
open GraphVerifier.Runtime
set_option maxHeartbeats 800000

def entry (i j : ℕ) : BitString := if i=j then signedBits 1 else signedBits 0
def comparison : Fin 6 ↪ Fin 25 where
  toFun i := ![1,2,10,11,12,13] i
  inj' := by decide +kernel
noncomputable def zeroWord : OracleBlock 24 := push 3 false
noncomputable def oneWord : OracleBlock 24 := seq (push 3 true) (push 3 false)
noncomputable def select : OracleBlock 24 := branchPop 10 zeroWord zeroWord oneWord
noncomputable def cell : OracleBlock 24 := seq (readLengthOn comparison) select
noncomputable def program : OracleBlock 24 := WordMatrixEmitter.arrayBlock cell
noncomputable def time : Polynomial ℕ := X^2*(26*X+89)+46*X+44

lemma select_executes (g : BitString → ℕ) (s : Store 24) (i j : ℕ)
    (hs : s 3=[]) (hf : s 10=[]) :
    ∃c,select.Executes g (Function.update s 10 [decide (i=j)])
      (Function.update s 3 (entry i j)) c ∧ c ≤ 6 := by
  have he : Function.update (Function.update s (10:Fin 25) [decide (i=j)]) 10 []=s := by
    simp only [Function.update_idem,←hf,Function.update_eq_self]
  by_cases hij : i=j
  · have h1 : oneWord.Executes g s (Function.update s 3 (signedBits 1)) 4 := by
      have hh := seq_executes _ _ g (push_executes g (3:Fin 25) true s)
        (push_executes g (3:Fin 25) false (Function.update s 3 (true::s 3)))
      simpa [oneWord,hs] using hh
    refine ⟨6,?_,by omega⟩
    apply branchPop_true (10:Fin 25) zeroWord zeroWord oneWord g (rest := []) (by simp [hij])
    simpa only [he,entry,if_pos hij] using h1
  · have h0 : zeroWord.Executes g s (Function.update s 3 (signedBits 0)) 1 := by
      simpa [zeroWord,hs] using push_executes g (3:Fin 25) false s
    refine ⟨3,?_,by omega⟩
    apply branchPop_false (10:Fin 25) zeroWord zeroWord oneWord g (rest := []) (by simp [hij])
    simpa only [he,entry,if_neg hij] using h0

lemma cell_executes (g : BitString → ℕ) (n i j : ℕ) (out inner outer a b : BitString) :
    ∃c,cell.Executes g (MatrixEmitter.store n i j [] out inner outer (MatrixProduct.params a b))
      (MatrixEmitter.store n i j (entry i j) out inner outer (MatrixProduct.params a b)) c ∧
      c ≤ 13*(i+j)+31 := by
  let s := MatrixEmitter.store n i j [] out inner outer (MatrixProduct.params a b)
  obtain ⟨c,hc,hcb⟩ := readLengthOn_executes comparison g s (List.replicate i true) (List.replicate j true)
    (by funext r;fin_cases r <;> rfl)
  simp only [List.length_replicate] at hc hcb
  obtain ⟨d,hd,hdb⟩ := select_executes g s i j rfl rfl
  have he : Function.update s (3:Fin 25) (entry i j)=
      MatrixEmitter.store n i j (entry i j) out inner outer (MatrixProduct.params a b) := by
    exact WordMatrixEmitter.store_value _ _ _ _ _ _ _ _ _
  rw [he] at hd
  exact ⟨c+d+2,seq_executes _ _ g hc hd,by omega⟩

lemma entry_length (i j : ℕ) : (entry i j).length ≤ 2 := by unfold entry;split_ifs <;> decide
lemma words_eq (n : ℕ) : WordMatrixEmitter.matrixWords n entry=matrixWords (1:Matrix (Fin n) (Fin n) ℤ) := by
  apply emitter_matrixWords_of_entries
  intro i j
  by_cases h:i.val=j.val <;> simp [entry,Matrix.one_apply,Fin.ext_iff,h]

theorem executes (g : BitString → ℕ) (n : ℕ) (a b : BitString) :
    ∃c,program.Executes g (MatrixProduct.store n a b [])
      (MatrixProduct.store n a b (encodeBitList (matrixWords (1:Matrix (Fin n) (Fin n) ℤ)))) c ∧ c ≤ time.eval n := by
  obtain ⟨c,hc,hcb⟩ := WordMatrixEmitter.arrayBlock_executes cell entry n (26*n+45) 2 (MatrixProduct.params a b)
    (by intro g i j out inner outer hi hj;obtain ⟨c,hc,hcb⟩ := cell_executes g n i j out inner outer a b
        exact ⟨c,hc,hcb.trans (by omega)⟩) (by intros;exact entry_length _ _) g
  rw [words_eq,MatrixProduct.emitter_output,←MatrixProduct.store_emitter] at hc
  refine ⟨c,hc,hcb.trans ?_⟩
  simp only [time,eval_add,eval_mul,eval_pow,eval_X,eval_ofNat]
  nlinarith
lemma cell_queryFree : cell.QueryFree := seq_queryFree _ _ (readLengthOn_queryFree _)
  (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _)
    (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))
lemma queryFree : program.QueryFree := WordMatrixEmitter.arrayBlock_queryFree cell cell_queryFree
noncomputable def on {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : OracleBlock k := rename program φ
theorem on_executes {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) (g : BitString → ℕ) (n : ℕ)
    (a b : BitString) (s : Store k) (hs : s∘φ=MatrixProduct.store n a b []) :
    ∃c,(on φ).Executes g s (Function.update s (φ 7) (encodeBitList (matrixWords (1:Matrix (Fin n) (Fin n) ℤ)))) c ∧ c ≤ time.eval n := by
  obtain ⟨c,hc,hcb⟩ := executes g n a b
  refine ⟨c,?_,hcb⟩
  apply rename_executes_to program φ g hc hs
  · funext i
    have hi := congrFun hs i
    simp only [Function.comp_def] at hi ⊢
    by_cases h:i=7
    · subst i;simp [MatrixProduct.store]
    · simp only [Function.update_of_ne (φ.injective.ne h),hi]
      have hv : i.val≠7 := fun hv => h (Fin.ext hv)
      simp [MatrixProduct.store,hv]
  · intro i hi;exact Function.update_of_ne (hi 7).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 25 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ queryFree
end HiddenCircuits.Complexity.DeterminantRuntime.IdentityMatrix
