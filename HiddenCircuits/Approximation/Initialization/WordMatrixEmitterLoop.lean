import HiddenCircuits.Approximation.Initialization.WordMatrixEmitterRows
namespace HiddenCircuits.Approximation.Initialization.WordMatrixEmitter
open Complexity OracleBlock MatrixEmitter
variable {k : ℕ}
noncomputable def rowsBody (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  seq copyInner (seq (rowLoop B) (seq (clear (port 2)) (push (port 1) true)))
noncomputable def rowsLoop (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  whilePop (port 6) (rowsBody B) (rowsBody B)

def rowsOutput (entry : ℕ → ℕ → BitString) (n : ℕ) : ℕ → ℕ → BitString → BitString
  | _,0,out => out
  | i,m+1,out => rowsOutput entry n (i+1) m (rowOutput entry i 0 n out)

 theorem rowsBody_executes (B : OracleBlock (k+7)) (entry : ℕ → ℕ → BitString)
    (n T W : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j (entry i j) out inner outer params) c ∧ c≤T)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W)
    (g : BitString → ℕ) (i : ℕ) (out outer : BitString) (hi : i<n) :
    ∃ c, (rowsBody B).Executes g (store n i 0 [] out [] outer params)
      (store n (i+1) 0 [] (rowOutput entry i 0 n out) [] outer params) c ∧ c≤n*(T+6*W+20)+11 := by
  obtain ⟨c,hc,hcb⟩ := row_loop B entry n T W params hB hW g i 0 n out outer hi (by omega)
  have hrow := whilePop_executes _ _ _ g hc
  simp only [Nat.zero_add] at hrow
  have hclean := seq_executes _ _ g
    (clearColumn_executes g n i n [] (rowOutput entry i 0 n out) [] outer params)
    (incrementRow_executes g n i 0 [] (rowOutput entry i 0 n out) [] outer params)
  have hh := seq_executes _ _ g (copyInner_executes g n i 0 [] out outer params)
    (seq_executes _ _ g hrow hclean)
  refine ⟨5*n+2+(c+(n+1+1+2)+2)+2,hh,?_⟩
  nlinarith

 theorem rows_loop (B : OracleBlock (k+7)) (entry : ℕ → ℕ → BitString)
    (n T W : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j (entry i j) out inner outer params) c ∧ c≤T)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W)
    (g : BitString → ℕ) (i m : ℕ) (out : BitString) (him : i+m≤n) :
    ∃ c, WhileExecution (port 6) (rowsBody B) (rowsBody B) g
      (store n i 0 [] out [] (List.replicate m true) params)
      (store n (i+m) 0 [] (rowsOutput entry n i m out) [] [] params) c ∧ c≤m*(n*(T+6*W+20)+13)+1 := by
  induction m generalizing i out with
  | zero =>
    refine ⟨1,?_,by simp⟩
    simpa [rowsOutput] using (WhileExecution.empty (stack := port 6) (B := rowsBody B) (C := rowsBody B)
      (g := g) (store n i 0 [] out [] [] params) (by simp))
  | succ m ih =>
    obtain ⟨c,hc,hcb⟩ := rowsBody_executes B entry n T W params hB hW g i out (List.replicate m true) (by omega)
    obtain ⟨d,hd,hdb⟩ := ih (i+1) (rowOutput entry i 0 n out) (by omega)
    have he : Function.update (store n i 0 [] out [] (List.replicate (m+1) true) params) (port 6) (List.replicate m true)=
        store n i 0 [] out [] (List.replicate m true) params := store_outer _ _ _ _ _ _ _ _ _
    have hh := WhileExecution.one
      (stack := port 6) (B := rowsBody B) (C := rowsBody B) (g := g)
      (show store n i 0 [] out [] (List.replicate (m+1) true) params (port 6)=true::List.replicate m true by simp [List.replicate_succ])
      (by rw [he];exact hc) hd
    refine ⟨1+c+1+d,?_,?_⟩
    · convert hh using 1 <;> simp [rowsOutput,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    · nlinarith

end HiddenCircuits.Approximation.Initialization.WordMatrixEmitter
