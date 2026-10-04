import HiddenCircuits.Circuit.Runtime.ProjectionStreamFilter
import HiddenCircuits.Complexity.GraphVerifier.UnaryProduct
import HiddenCircuits.Complexity.OracleMove

namespace HiddenCircuits.Circuit.Runtime.ProjectionStream
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.GraphVerifier.Runtime

def productEmbedding : Fin 4 ↪ Fin 11 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 4 else if i.val=2 then 5 else 6
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def copyN3 : OracleBlock 10 := copyOn 0 3 7 (by decide) (by decide) (by decide)
noncomputable def copyN4 : OracleBlock 10 := copyOn 0 4 7 (by decide) (by decide) (by decide)
noncomputable def product : OracleBlock 10 := rename repeatCopyBlock productEmbedding
noncomputable def prepare : OracleBlock 10 := seq copyN3 (seq (popDrop 3) (seq copyN4
  (seq product (seq (clear 3) (seq (repeatPrepend 5 4 [true,true])
    (seq (prepend 4 [true,true]) (moveOn 4 5 7 (by decide) (by decide) (by decide))))))))

theorem prepare_executes (oracle : BitString → ℕ) (n : ℕ) (out exponent : BitString) :
    ∃t, prepare.Executes oracle (store n 0 0 0 out exponent)
      (store n 0 0 (globalProjectionExponent n) out exponent) t ∧ t≤100*(n+1)^2 := by
  have h₁ : copyN3.Executes oracle (store n 0 0 0 out exponent) (store n n 0 0 out exponent) (5*n+2) := by
    convert copyOn_executes oracle (0:Fin 11) 3 7 (by decide) (by decide) (by decide) (store n 0 0 0 out exponent) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₂ : (popDrop (3:Fin 11)).Executes oracle (store n n 0 0 out exponent) (store n (n-1) 0 0 out exponent) 1 := by
    convert popDrop_executes (3:Fin 11) oracle (store n n 0 0 out exponent) using 1
    funext i;fin_cases i <;> simp [store,List.tail_replicate]
  have h₃ : copyN4.Executes oracle (store n (n-1) 0 0 out exponent) (store n (n-1) n 0 out exponent) (5*n+2) := by
    convert copyOn_executes oracle (0:Fin 11) 4 7 (by decide) (by decide) (by decide) (store n (n-1) 0 0 out exponent) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₄ : product.Executes oracle (store n (n-1) n 0 out exponent)
      (store n (n-1) 0 (n*(n-1)) out exponent) (n*(5*(n-1)+4)+1) := by
    apply rename_executes_to repeatCopyBlock productEmbedding oracle (unaryProduct_execution oracle (n-1) n)
    · funext i;fin_cases i <;> simp [store,productEmbedding,repeatCopyStore] <;> rfl
    · funext i;fin_cases i <;> simp [store,productEmbedding,repeatCopyStore] <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  have h₅ : (clear (3:Fin 11)).Executes oracle (store n (n-1) 0 (n*(n-1)) out exponent)
      (store n 0 0 (n*(n-1)) out exponent) (n-1+1) := by
    convert clear_executes oracle (3:Fin 11) (store n (n-1) 0 (n*(n-1)) out exponent) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have h₆ : (repeatPrepend (5:Fin 11) 4 [true,true]).Executes oracle (store n 0 0 (n*(n-1)) out exponent)
      (store n 0 (2*n*(n-1)) 0 out exponent) (9*(n*(n-1))+1) := by
    have hflat (r : ℕ) : (List.replicate r [true,true]).flatten=List.replicate (2*r) true := by
      change (List.replicate r (List.replicate 2 true)).flatten=_
      rw [List.flatten_replicate_replicate,Nat.mul_comm]
    convert repeatPrepend_executes oracle (5:Fin 11) 4 (by decide) [true,true]
      (store n 0 0 (n*(n-1)) out exponent) using 1
    · funext i;fin_cases i <;> simp [store,hflat,Nat.mul_assoc]
    · simp [store]
  have h₇ : (prepend (4:Fin 11) [true,true]).Executes oracle (store n 0 (2*n*(n-1)) 0 out exponent)
      (store n 0 (globalProjectionExponent n) 0 out exponent) 7 := by
    convert prepend_executes oracle (4:Fin 11) [true,true] (store n 0 (2*n*(n-1)) 0 out exponent) using 1
    funext i;fin_cases i <;> simp [store,globalProjectionExponent,List.replicate_succ]
  have h₈ : (moveOn (4:Fin 11) 5 7 (by decide) (by decide) (by decide)).Executes oracle
      (store n 0 (globalProjectionExponent n) 0 out exponent) (store n 0 0 (globalProjectionExponent n) out exponent)
      (6*globalProjectionExponent n+5) := by
    convert moveOn_executes oracle (4:Fin 11) 5 7 (by decide) (by decide) (by decide)
      (store n 0 (globalProjectionExponent n) 0 out exponent) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  refine ⟨_,seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ (seq_executes _ _ oracle h₃
    (seq_executes _ _ oracle h₄ (seq_executes _ _ oracle h₅ (seq_executes _ _ oracle h₆
      (seq_executes _ _ oracle h₇ h₈)))))),?_⟩
  unfold globalProjectionExponent
  have hh : n-1≤n := Nat.sub_le _ _
  have hm := Nat.mul_le_mul_left n hh
  nlinarith

theorem prepare_queryFree : prepare.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (popDrop_queryFree _)
    (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rename_queryFree _ _ repeatCopy_queryFree)
      (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _)
        (seq_queryFree _ _ (prepend_queryFree _ _) (moveOn_queryFree _ _ _ _ _ _)))))))
end HiddenCircuits.Circuit.Runtime.ProjectionStream
