import HiddenCircuits.Complexity.MatrixEmitter
import HiddenCircuits.Complexity.CNFEmitter

namespace HiddenCircuits.Complexity.MatrixEmitter
open OracleBlock
variable {k : ℕ}

theorem store_outer (n i j : ℕ) (bit out inner outer next : BitString) (params : Store (k+7)) :
    Function.update (store n i j bit out inner outer params) (port 6) next=store n i j bit out inner next params := by
  funext r;simp [store,Function.update_apply];split_ifs <;> simp_all [port]
theorem store_output (n i j : ℕ) (bit out inner outer next : BitString) (params : Store (k+7)) :
    Function.update (store n i j bit out inner outer params) (port 4) next=store n i j bit next inner outer params := by
  funext r;simp [store,Function.update_apply];split_ifs <;> simp_all [port]
theorem store_column_zero (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) :
    Function.update (store n i j bit out inner outer params) (port 2) []=store n i 0 bit out inner outer params := by
  funext r;simp [store,Function.update_apply];split_ifs <;> simp_all [port]
theorem store_row (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) :
    Function.update (store n i j bit out inner outer params) (port 1) (true::List.replicate i true)=store n (i+1) j bit out inner outer params := by
  funext r;simp [store,Function.update_apply,List.replicate_succ];split_ifs <;> simp_all [port]
theorem store_row_zero (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) :
    Function.update (store n i j bit out inner outer params) (port 1) []=store n 0 j bit out inner outer params := by
  funext r;simp [store,Function.update_apply];split_ifs <;> simp_all [port]

noncomputable def copyInner : OracleBlock (k+7) := copyOn (port 0) (port 5) (port 7) (by simp [port]) (by simp [port]) (by simp [port])
noncomputable def copyOuter : OracleBlock (k+7) := copyOn (port 0) (port 6) (port 7) (by simp [port]) (by simp [port]) (by simp [port])

 theorem copyInner_executes (g : BitString → ℕ) (n i j : ℕ) (bit out outer : BitString) (params : Store (k+7)) :
    copyInner.Executes g (store n i j bit out [] outer params)
      (store n i j bit out (List.replicate n true) outer params) (5*n+2) := by
  have hh := copyOn_executes g (port 0) (port 5) (port 7) (by simp [port]) (by simp [port]) (by simp [port])
    (store n i j bit out [] outer params) (by simp)
  simpa [store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,List.append_nil,List.length_replicate,store_inner] using hh

 theorem copyOuter_executes (g : BitString → ℕ) (n i j : ℕ) (bit out inner : BitString) (params : Store (k+7)) :
    copyOuter.Executes g (store n i j bit out inner [] params)
      (store n i j bit out inner (List.replicate n true) params) (5*n+2) := by
  have hh := copyOn_executes g (port 0) (port 6) (port 7) (by simp [port]) (by simp [port]) (by simp [port])
    (store n i j bit out inner [] params) (by simp)
  simpa [store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,List.append_nil,List.length_replicate,store_outer] using hh

 theorem clearColumn_executes (g : BitString → ℕ) (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) :
    (clear (port 2)).Executes g (store n i j bit out inner outer params)
      (store n i 0 bit out inner outer params) (j+1) := by
  have hh := clear_executes g (port 2) (store n i j bit out inner outer params)
  simpa [store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,List.length_replicate,store_column_zero] using hh

 theorem incrementRow_executes (g : BitString → ℕ) (n i j : ℕ) (bit out inner outer : BitString) (params : Store (k+7)) :
    (push (port 1) true).Executes g (store n i j bit out inner outer params)
      (store n (i+1) j bit out inner outer params) 1 := by
  have hh := push_executes g (port 1) true (store n i j bit out inner outer params)
  simpa [store_core,Matrix.cons_val_zero,Matrix.cons_val_succ,store_row] using hh

noncomputable def rowsBody (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  seq copyInner (seq (rowLoop B) (seq (clear (port 2)) (push (port 1) true)))
noncomputable def rowsLoop (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  whilePop (port 6) (rowsBody B) (rowsBody B)

def rowsOutput (edge : ℕ → ℕ → Bool) (n : ℕ) : ℕ → ℕ → BitString → BitString
  | _,0,out => out
  | i,m+1,out => rowsOutput edge n (i+1) m (rowOutput edge i 0 n out)

 theorem rowsBody_executes (B : OracleBlock (k+7)) (edge : ℕ → ℕ → Bool)
    (n T : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString → ℕ) (i : ℕ) (out outer : BitString) (hi : i<n) :
    ∃ c, (rowsBody B).Executes g (store n i 0 [] out [] outer params)
      (store n (i+1) 0 [] (rowOutput edge i 0 n out) [] outer params) c ∧ c≤n*T+16*n+11 := by
  obtain ⟨c,hc,hcb⟩ := row_loop B edge n T params hB g i 0 n out outer hi (by omega)
  have hrow := whilePop_executes _ _ _ g hc
  simp only [Nat.zero_add] at hrow
  have hclean := seq_executes _ _ g
    (clearColumn_executes g n i n [] (rowOutput edge i 0 n out) [] outer params)
    (incrementRow_executes g n i 0 [] (rowOutput edge i 0 n out) [] outer params)
  have hh := seq_executes _ _ g (copyInner_executes g n i 0 [] out outer params)
    (seq_executes _ _ g hrow hclean)
  refine ⟨5*n+2+(c+(n+1+1+2)+2)+2,hh,?_⟩
  nlinarith

 theorem rows_loop (B : OracleBlock (k+7)) (edge : ℕ → ℕ → Bool)
    (n T : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString → ℕ) (i m : ℕ) (out : BitString) (him : i+m≤n) :
    ∃ c, WhileExecution (port 6) (rowsBody B) (rowsBody B) g
      (store n i 0 [] out [] (List.replicate m true) params)
      (store n (i+m) 0 [] (rowsOutput edge n i m out) [] [] params) c ∧ c≤m*(n*T+16*n+13)+1 := by
  induction m generalizing i out with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [rowsOutput] using (WhileExecution.empty (stack := port 6) (B := rowsBody B) (C := rowsBody B)
      (g := g) (store n i 0 [] out [] [] params) (by simp))
  | succ m ih =>
    obtain ⟨c,hc,hcb⟩ := rowsBody_executes B edge n T params hB g i out (List.replicate m true) (by omega)
    obtain ⟨d,hd,hdb⟩ := ih (i+1) (rowOutput edge i 0 n out) (by omega)
    have he : Function.update (store n i 0 [] out [] (List.replicate (m+1) true) params) (port 6) (List.replicate m true)=
        store n i 0 [] out [] (List.replicate m true) params := store_outer _ _ _ _ _ _ _ _ _
    have hh := WhileExecution.one
      (stack := port 6) (B := rowsBody B) (C := rowsBody B) (g := g)
      (show store n i 0 [] out [] (List.replicate (m+1) true) params (port 6)=true::List.replicate m true by simp [List.replicate_succ])
      (by rw [he];exact hc) hd
    refine ⟨1+c+1+d,?_,?_⟩
    · convert hh using 1 <;> simp [rowsOutput,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    · nlinarith

end HiddenCircuits.Complexity.MatrixEmitter
