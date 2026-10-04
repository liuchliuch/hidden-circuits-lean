import HiddenCircuits.Complexity.MatrixEmitterRows
import HiddenCircuits.Complexity.GraphEncoding

namespace HiddenCircuits.Complexity.MatrixEmitter
open OracleBlock
variable {k : ℕ}

def matrixBits (n : ℕ) (edge : ℕ → ℕ → Bool) : BitString :=
  (List.range n).flatMap (fun i => (List.range n).map (edge i))
def queryBits (n : ℕ) (edge : ℕ → ℕ → Bool) : BitString :=
  pairBits (List.replicate n true) (matrixBits n edge)

theorem rowOutput_eq (edge : ℕ → ℕ → Bool) (i j m : ℕ) (out : BitString) :
    rowOutput edge i j m out=((List.range' j m).map (edge i)).reverse++out := by
  induction m generalizing j out with
  | zero => simp [rowOutput]
  | succ m ih => simp [rowOutput,List.range'_succ,ih,List.reverse_cons,List.append_assoc]

theorem rowsOutput_eq (edge : ℕ → ℕ → Bool) (n i m : ℕ) (out : BitString) :
    rowsOutput edge n i m out=
      ((List.range' i m).flatMap (fun r => (List.range n).map (edge r))).reverse++out := by
  induction m generalizing i out with
  | zero => simp [rowsOutput]
  | succ m ih =>
    simp [rowsOutput,ih,rowOutput_eq,List.range'_succ,List.reverse_append,List.append_assoc,←List.range_eq_range']

@[simp] theorem matrixBits_length (n : ℕ) (edge : ℕ → ℕ → Bool) : (matrixBits n edge).length=n*n := by
  simp [matrixBits,List.length_flatMap]

@[simp] theorem queryBits_length (n : ℕ) (edge : ℕ → ℕ → Bool) : (queryBits n edge).length=2*n+n*n+1 := by
  simp [queryBits]

 theorem pairBits_append (x y : BitString) : pairBits x y=pairBits x []++y := by
  induction x <;> simp [pairBits, *]

 theorem unary_header (n : ℕ) : pairBits (List.replicate n true) []=List.replicate (2*n) true++[false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,pairBits,ih]
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [List.replicate_succ,List.cons_append]

 theorem query_reverse (n : ℕ) (edge : ℕ → ℕ → Bool) :
    (queryBits n edge).reverse=(matrixBits n edge).reverse++false::List.replicate (2*n) true := by
  rw [queryBits,pairBits_append,unary_header]
  simp [List.reverse_append]

noncomputable def headerBlock : OracleBlock (k+7) :=
  seq copyInner (CNFEmitter.header (port 5) (port 4))

 theorem headerBlock_executes (g : BitString → ℕ) (n : ℕ) (params : Store (k+7)) :
    headerBlock.Executes g (store n 0 0 [] [] [] [] params)
      (store n 0 0 [] (false::List.replicate (2*n) true) [] [] params) (14*n+8) := by
  have h₁ := copyInner_executes g n 0 0 [] [] [] params
  have h₂ := CNFEmitter.header_executes g (port 5) (port 4) (by simp [port])
    (store n 0 0 [] [] (List.replicate n true) [] params)
  have h₂' : (CNFEmitter.header (port 5) (port 4)).Executes g
      (store n 0 0 [] [] (List.replicate n true) [] params)
      (store n 0 0 [] (false::List.replicate (2*n) true) [] [] params) (9*n+4) := by
    simpa [store_core,store_inner,store_output] using h₂
  convert seq_executes _ _ g h₁ h₂' using 1 <;> omega

noncomputable def finishBlock : OracleBlock (k+7) :=
  seq (clear (port 1)) (reverseOn (port 4) (port 7) (by simp [port]))

 theorem finishBlock_executes (g : BitString → ℕ) (n i : ℕ) (out : BitString) (params : Store (k+7)) :
    finishBlock.Executes g (store n i 0 [] out [] [] params)
      (Function.update (store n 0 0 [] [] [] [] params) (port 7) out.reverse) (i+2*out.length+4) := by
  have h₁ : (clear (port 1)).Executes g (store n i 0 [] out [] [] params)
      (store n 0 0 [] out [] [] params) (i+1) := by
    simpa [store_core,store_row_zero] using clear_executes g (port 1) (store n i 0 [] out [] [] params)
  have h₂ := reverseOn_executes g (port 4) (port 7) (by simp [port]) (store n 0 0 [] out [] [] params)
  have h₂' : (reverseOn (port 4) (port 7) (by simp [port])).Executes g (store n 0 0 [] out [] [] params)
      (Function.update (store n 0 0 [] [] [] [] params) (port 7) out.reverse) (2*out.length+1) := by
    simpa [store_core,store_output] using h₂
  convert seq_executes _ _ g h₁ h₂' using 1 <;> omega

noncomputable def block (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  seq headerBlock (seq copyOuter (seq (rowsLoop B) finishBlock))

/-- One actual finite program emits the entire row-major binary query, with an explicit instruction bound. -/
theorem block_executes (B : OracleBlock (k+7)) (edge : ℕ → ℕ → Bool)
    (n T : ℕ) (params : Store (k+7))
    (hB : ∀ g i j out inner outer, i<n → j<n →
      ∃ c, B.Executes g (store n i j [] out inner outer params)
        (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString → ℕ) :
    ∃ c, (block B).Executes g (store n 0 0 [] [] [] [] params)
      (Function.update (store n 0 0 [] [] [] [] params) (port 7) (queryBits n edge)) c ∧
      c≤n*n*(T+18)+40*n+30 := by
  let pre : BitString := false::List.replicate (2*n) true
  obtain ⟨c,hc,hcb⟩ := rows_loop B edge n T params hB g 0 n pre (by omega)
  have hrows := whilePop_executes _ _ _ g hc
  have he : rowsOutput edge n 0 n pre=(queryBits n edge).reverse := by
    rw [rowsOutput_eq,←List.range_eq_range']
    exact (query_reverse n edge).symm
  simp only [Nat.zero_add,he] at hrows
  have hf := finishBlock_executes g n n (queryBits n edge).reverse params
  simp only [List.reverse_reverse,List.length_reverse] at hf
  have hh := seq_executes _ _ g (headerBlock_executes g n params)
    (seq_executes _ _ g (copyOuter_executes g n 0 0 [] pre [] params)
      (seq_executes _ _ g hrows hf))
  refine ⟨14*n+8+(5*n+2+(c+(n+2*(queryBits n edge).length+4)+2)+2)+2,hh,?_⟩
  rw [queryBits_length]
  nlinarith

 theorem block_queryFree (B : OracleBlock (k+7)) (hB : B.QueryFree) : (block B).QueryFree := by
  have he : (emitBit (k:=k)).QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree (push_queryFree _ _) (push_queryFree _ _)
  have hentry : (entryBody B).QueryFree := seq_queryFree _ _ hB (seq_queryFree _ _ he (push_queryFree _ _))
  have hrow : (rowLoop B).QueryFree := whilePop_queryFree _ _ _ hentry hentry
  have hrowsbody : (rowsBody B).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ hrow (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
  have hrows : (rowsLoop B).QueryFree := whilePop_queryFree _ _ _ hrowsbody hrowsbody
  have hhead : (headerBlock (k:=k)).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (CNFEmitter.header_queryFree _ _)
  have hf : (finishBlock (k:=k)).QueryFree := seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)
  exact seq_queryFree _ _ hhead (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ hrows hf))

end HiddenCircuits.Complexity.MatrixEmitter
