import HiddenCircuits.Complexity.GraphVerifier.UnaryProduct
import HiddenCircuits.Complexity.OracleRepeat

/-! Actual unary clone-query dimensions, with all formula/descriptor tapes framed. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.Size
open OracleBlock
open GraphVerifier.Runtime

def store (n m a b N cut c d : ℕ) (params : Store 29) : Store 29 :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update params 0 (List.replicate N true))
      9 (List.replicate a true)) 10 (List.replicate b true)) 12 (List.replicate n true))
      13 (List.replicate m true)) 14 (List.replicate cut true)) 21 (List.replicate c true))
      22 (List.replicate d true)) 23 []) 24 []

def leftEmbedding : Fin 4 ↪ Fin 30 where
  toFun i := if i.val=0 then 22 else if i.val=1 then 21 else if i.val=2 then 14 else 23
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def rightEmbedding : Fin 4 ↪ Fin 30 where
  toFun i := if i.val=0 then 10 else if i.val=1 then 21 else if i.val=2 then 0 else 23
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def leftProduct : OracleBlock 29 := rename repeatCopyBlock leftEmbedding
noncomputable def rightProduct : OracleBlock 29 := rename repeatCopyBlock rightEmbedding
noncomputable def copyN : OracleBlock 29 := copyOn 12 21 24 (by decide) (by decide) (by decide)
noncomputable def doubleN : OracleBlock 29 := repeatPrepend 21 22 [true,true]
noncomputable def copyA : OracleBlock 29 := copyOn 9 21 24 (by decide) (by decide) (by decide)
noncomputable def copyCut : OracleBlock 29 := copyOn 14 0 24 (by decide) (by decide) (by decide)
noncomputable def copyM : OracleBlock 29 := copyOn 13 21 24 (by decide) (by decide) (by decide)

 theorem copyN_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    copyN.Executes g (store n m a b 0 0 0 0 params) (store n m a b 0 0 n 0 params) (5*n+2) := by
  convert copyOn_executes g (12:Fin 30) 21 24 (by decide) (by decide) (by decide)
    (store n m a b 0 0 0 0 params) (by simp [store]) using 1
  · funext i;fin_cases i <;> simp [store]
  · simp [store]

 theorem doubleN_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    doubleN.Executes g (store n m a b 0 0 n 0 params) (store n m a b 0 0 0 (2*n) params) (9*n+1) := by
  have hh := repeatPrepend_executes g (21:Fin 30) 22 (by decide) [true,true] (store n m a b 0 0 n 0 params)
  rw [show [true,true]=List.replicate 2 true from rfl] at hh
  have hp (r : ℕ) : (List.replicate r [true,true]).flatten=List.replicate (2*r) true := by
    change (List.replicate r (List.replicate 2 true)).flatten=_
    rw [List.flatten_replicate_replicate]
    congr 1
    omega
  convert hh using 1
  · funext i;fin_cases i <;> simp [store,hp,Nat.mul_comm]
  · simp [store] <;> ring

 theorem copyA_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    copyA.Executes g (store n m a b 0 0 0 (2*n) params) (store n m a b 0 0 a (2*n) params) (5*a+2) := by
  convert copyOn_executes g (9:Fin 30) 21 24 (by decide) (by decide) (by decide)
    (store n m a b 0 0 0 (2*n) params) (by simp [store]) using 1
  · funext i;fin_cases i <;> simp [store]
  · simp [store]

 theorem leftProduct_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    leftProduct.Executes g (store n m a b 0 0 a (2*n) params)
      (store n m a b 0 (2*n*a) 0 (2*n) params) (a*(10*n+4)+1) := by
  have hh := unaryProduct_execution g (2*n) a
  have hr := rename_executes_to repeatCopyBlock leftEmbedding g hh
    (outerS := store n m a b 0 0 a (2*n) params) (outerT := store n m a b 0 (2*n*a) 0 (2*n) params)
    (by funext i;fin_cases i <;> simp [store,leftEmbedding,repeatCopyStore] <;> rfl)
    (by funext i;fin_cases i <;> simp [store,leftEmbedding,repeatCopyStore,Nat.mul_comm,Nat.mul_left_comm] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl))
  convert hr using 1 <;> ring

 theorem clearDouble_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    (clear (22:Fin 30)).Executes g (store n m a b 0 (2*n*a) 0 (2*n) params)
      (store n m a b 0 (2*n*a) 0 0 params) (2*n+1) := by
  convert clear_executes g (22:Fin 30) (store n m a b 0 (2*n*a) 0 (2*n) params) using 1
  · funext i;fin_cases i <;> simp [store]
  · simp [store]

 theorem copyCut_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    copyCut.Executes g (store n m a b 0 (2*n*a) 0 0 params)
      (store n m a b (2*n*a) (2*n*a) 0 0 params) (5*(2*n*a)+2) := by
  convert copyOn_executes g (14:Fin 30) 0 24 (by decide) (by decide) (by decide)
    (store n m a b 0 (2*n*a) 0 0 params) (by simp [store]) using 1
  · funext i;fin_cases i <;> simp [store]
  · simp [store]

 theorem copyM_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    copyM.Executes g (store n m a b (2*n*a) (2*n*a) 0 0 params)
      (store n m a b (2*n*a) (2*n*a) m 0 params) (5*m+2) := by
  convert copyOn_executes g (13:Fin 30) 21 24 (by decide) (by decide) (by decide)
    (store n m a b (2*n*a) (2*n*a) 0 0 params) (by simp [store]) using 1
  · funext i;fin_cases i <;> simp [store]
  · simp [store]

set_option maxHeartbeats 1600000 in
 theorem rightProduct_executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    rightProduct.Executes g (store n m a b (2*n*a) (2*n*a) m 0 params)
      (store n m a b (2*n*a+m*b) (2*n*a) 0 0 params) (m*(5*b+4)+1) := by
  have hh := repeatCopy_execution g (List.replicate b true) (List.replicate m true) (List.replicate (2*n*a) true)
  simp only [List.length_replicate,repeatPrefix_unary] at hh
  have hr := rename_executes_to repeatCopyBlock rightEmbedding g hh
    (outerS := store n m a b (2*n*a) (2*n*a) m 0 params)
    (outerT := store n m a b (2*n*a+m*b) (2*n*a) 0 0 params)
    (by funext i;fin_cases i <;> simp [store,rightEmbedding,repeatCopyStore] <;> rfl)
    (by funext i;fin_cases i <;> simp [store,rightEmbedding,repeatCopyStore,Nat.add_comm] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl))
  exact hr

noncomputable def block : OracleBlock 29 :=
  seq copyN (seq doubleN (seq copyA (seq leftProduct (seq (clear 22) (seq copyCut (seq copyM rightProduct))))))

 theorem executes (g : BitString → ℕ) (n m a b : ℕ) (params : Store 29) :
    block.Executes g (store n m a b 0 0 0 0 params)
      (store n m a b (2*n*a+m*b) (2*n*a) 0 0 params)
      (20*n*a+5*m*b+16*n+9*m+9*a+26) := by
  have hh := seq_executes _ _ g (copyN_executes g n m a b params)
    (seq_executes _ _ g (doubleN_executes g n m a b params)
      (seq_executes _ _ g (copyA_executes g n m a b params)
        (seq_executes _ _ g (leftProduct_executes g n m a b params)
          (seq_executes _ _ g (clearDouble_executes g n m a b params)
            (seq_executes _ _ g (copyCut_executes g n m a b params)
              (seq_executes _ _ g (copyM_executes g n m a b params) (rightProduct_executes g n m a b params)))))))
  convert hh using 1 <;> ring

 theorem cost_bound (n m a b : ℕ) :
    20*n*a+5*m*b+16*n+9*m+9*a+26≤100*(n+m+a+b+1)^2 := by
  have hn : n≤n+m+a+b := by omega
  have hm : m≤n+m+a+b := by omega
  have ha : a≤n+m+a+b := by omega
  have hb : b≤n+m+a+b := by omega
  have hna := Nat.mul_le_mul hn ha
  have hmb := Nat.mul_le_mul hm hb
  nlinarith

 theorem queryFree : block.QueryFree := by
  have hN : copyN.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hD : doubleN.QueryFree := repeatPrepend_queryFree _ _ _
  have hA : copyA.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hL : leftProduct.QueryFree := rename_queryFree _ _ repeatCopy_queryFree
  have hC : copyCut.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hM : copyM.QueryFree := copyOn_queryFree _ _ _ _ _ _
  have hR : rightProduct.QueryFree := rename_queryFree _ _ repeatCopy_queryFree
  exact seq_queryFree _ _ hN (seq_queryFree _ _ hD (seq_queryFree _ _ hA
    (seq_queryFree _ _ hL (seq_queryFree _ _ (clear_queryFree _)
      (seq_queryFree _ _ hC (seq_queryFree _ _ hM hR))))))

end HiddenCircuits.Complexity.CNFCloneEmitter.Size
