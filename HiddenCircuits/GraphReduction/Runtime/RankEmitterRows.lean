import HiddenCircuits.GraphReduction.Runtime.RankEmitter

namespace HiddenCircuits.GraphReduction.Runtime.RankEmitter
open Complexity OracleBlock MatrixEmitter BinaryArithmetic
variable {k : ℕ}
set_option maxHeartbeats 800000

def rowWord (edge : ℕ→ℕ→Bool) (n i : ℕ) : BitString := wordChunk (List.replicate (rowCount edge i 0 n) true)

lemma rowWord_reverse (edge : ℕ→ℕ→Bool) (n i : ℕ) (out : BitString) :
    (rowWord edge n i).reverse++out=false::rowOutput edge i 0 n (true::out) := by
  rw [rowOutput_eq,rowWord,wordChunk,unary_header]
  simp [List.reverse_append,List.append_assoc]

lemma pushOutput_executes (g : BitString→ℕ) (n i j : ℕ) (b : Bool) (out inner outer : BitString) (params : Store (k+7)) :
    (push (port 4) b).Executes g (store n i j [] out inner outer params) (store n i j [] (b::out) inner outer params) 1 := by
  simpa only [store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,store_output] using push_executes g (port 4) b (store n i j [] out inner outer params)
noncomputable def rowsBody (B : OracleBlock (k+7)) : OracleBlock (k+7) := seq (push (port 4) true)
  (seq copyInner (seq (rowLoop B) (seq (clear (port 2)) (seq (push (port 4) false) (push (port 1) true)))))
noncomputable def rowsLoop (B : OracleBlock (k+7)) : OracleBlock (k+7) := whilePop (port 6) (rowsBody B) (rowsBody B)
def rowsOutput (edge : ℕ→ℕ→Bool) (n : ℕ) : ℕ→ℕ→BitString→BitString
  | _,0,out => out
  | i,m+1,out => rowsOutput edge n (i+1) m ((rowWord edge n i).reverse++out)

lemma rowsBody_executes (B : OracleBlock (k+7)) (edge : ℕ→ℕ→Bool) (n T : ℕ) (params : Store (k+7))
    (hB : ∀g i j out inner outer,i<n→j<n→∃c,B.Executes g (store n i j [] out inner outer params)
      (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString→ℕ) (i : ℕ) (out outer : BitString) (hi:i<n) :
    ∃c,(rowsBody B).Executes g (store n i 0 [] out [] outer params)
      (store n (i+1) 0 [] ((rowWord edge n i).reverse++out) [] outer params) c ∧ c≤n*(T+19)+17 := by
  have hs:=pushOutput_executes g n i 0 true out [] outer params
  have hc:=copyInner_executes g n i 0 [] (true::out) outer params
  obtain ⟨c,hr,hrb⟩:=row_loop B edge n T params hB g i 0 n (true::out) outer hi (by omega)
  have he:=whilePop_executes _ _ _ g hr
  simp only [Nat.zero_add] at he
  have hz:=clearColumn_executes g n i n [] (rowOutput edge i 0 n (true::out)) [] outer params
  have hd:=pushOutput_executes g n i 0 false (rowOutput edge i 0 n (true::out)) [] outer params
  have hi:=incrementRow_executes g n i 0 [] (false::rowOutput edge i 0 n (true::out)) [] outer params
  have hh:=seq_executes _ _ g hs (seq_executes _ _ g hc (seq_executes _ _ g he (seq_executes _ _ g hz (seq_executes _ _ g hd hi))))
  refine ⟨1+(5*n+2+(c+(n+1+(1+1+2)+2)+2)+2)+2,?_,by nlinarith⟩
  simpa only [rowWord_reverse] using hh

lemma rows_loop (B : OracleBlock (k+7)) (edge : ℕ→ℕ→Bool) (n T : ℕ) (params : Store (k+7))
    (hB : ∀g i j out inner outer,i<n→j<n→∃c,B.Executes g (store n i j [] out inner outer params)
      (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString→ℕ) (i m : ℕ) (out : BitString) (him:i+m≤n) :
    ∃c,WhileExecution (port 6) (rowsBody B) (rowsBody B) g (store n i 0 [] out [] (List.replicate m true) params)
      (store n (i+m) 0 [] (rowsOutput edge n i m out) [] [] params) c ∧ c≤m*(n*(T+19)+19)+1 := by
  induction m generalizing i out with
  | zero => exact ⟨1,by simpa [rowsOutput] using WhileExecution.empty (stack:=port 6) (B:=rowsBody B) (C:=rowsBody B) (g:=g) (store n i 0 [] out [] [] params) (by simp),by simp⟩
  | succ m ih =>
    obtain ⟨a,ha,hab⟩:=rowsBody_executes B edge n T params hB g i out (List.replicate m true) (by omega)
    obtain ⟨b,hb,hbb⟩:=ih (i+1) ((rowWord edge n i).reverse++out) (by omega)
    have he : Function.update (store n i 0 [] out [] (List.replicate (m+1) true) params) (port 6) (List.replicate m true)=store n i 0 [] out [] (List.replicate m true) params := store_outer _ _ _ _ _ _ _ _ _
    have hh:=WhileExecution.one (stack:=port 6) (B:=rowsBody B) (C:=rowsBody B) (g:=g)
      (show store n i 0 [] out [] (List.replicate (m+1) true) params (port 6)=true::List.replicate m true by simp [List.replicate_succ])
      (by rw [he];exact ha) hb
    refine ⟨1+a+1+b,?_,by nlinarith⟩
    convert hh using 1 <;> simp [rowsOutput,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
end HiddenCircuits.GraphReduction.Runtime.RankEmitter
