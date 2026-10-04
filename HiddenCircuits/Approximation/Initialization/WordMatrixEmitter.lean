import HiddenCircuits.Approximation.Initialization.WordMatrixEmitterLoop

/-! Fresh reconstruction: row-major word-array serialization, with optional
unary matrix header, exact framing and a charged polynomial instruction bound. -/
namespace HiddenCircuits.Approximation.Initialization.WordMatrixEmitter
open Complexity OracleBlock MatrixEmitter
variable {k : ℕ}

def matrixWords (n : ℕ) (entry : ℕ → ℕ → BitString) : List BitString :=
  (List.range n).flatMap (fun i => (List.range n).map (entry i))
def queryBits (n : ℕ) (entry : ℕ → ℕ → BitString) : BitString :=
  pairBits (List.replicate n true) (encodeBitList (matrixWords n entry))
lemma pair_append (x y z : BitString) : pairBits x (y++z)=pairBits x y++z := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [pairBits,ih,List.cons_append]
lemma encode_append (xs ys : List BitString) : encodeBitList (xs++ys)=encodeBitList xs++encodeBitList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,encodeBitList,ih,pair_append]
lemma encode_cons (x : BitString) (xs : List BitString) :
    encodeBitList (x::xs)=(true::pairBits x [])++encodeBitList xs := by
  simp only [encodeBitList,List.cons_append]
  rw [MatrixEmitter.pairBits_append]

lemma rowOutput_eq (entry : ℕ → ℕ → BitString) (i j m : ℕ) (out : BitString) :
    rowOutput entry i j m out=(encodeBitList ((List.range' j m).map (entry i))).reverse++out := by
  induction m generalizing j out with
  | zero => simp [rowOutput,encodeBitList]
  | succ m ih => simp [rowOutput,List.range'_succ,ih,encode_cons,List.reverse_append,List.append_assoc]
lemma rowsOutput_eq (entry : ℕ → ℕ → BitString) (n i m : ℕ) (out : BitString) :
    rowsOutput entry n i m out=
      (encodeBitList ((List.range' i m).flatMap (fun r => (List.range n).map (entry r)))).reverse++out := by
  induction m generalizing i out with
  | zero => simp [rowsOutput,encodeBitList]
  | succ m ih =>
    simp [rowsOutput,ih,rowOutput_eq,List.range'_succ,encode_append,List.reverse_append,List.append_assoc,←List.range_eq_range']
@[simp] lemma matrixWords_length (n : ℕ) (entry : ℕ → ℕ → BitString) :
    (matrixWords n entry).length=n*n := by simp [matrixWords,List.length_flatMap]
lemma encode_length_bound (xs : List BitString) (W : ℕ) (h : ∀x∈xs,x.length ≤ W) :
    (encodeBitList xs).length ≤ xs.length*(2*W+2) := by
  induction xs with
  | nil => simp [encodeBitList]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hi := ih (by intro y hy;exact h y (by simp [hy]))
    simp only [encodeBitList,List.length_cons,pairBits_length]
    nlinarith
lemma data_length_bound (n W : ℕ) (entry : ℕ → ℕ → BitString)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W) :
    (encodeBitList (matrixWords n entry)).length ≤ n*n*(2*W+2) := by
  rw [←matrixWords_length n entry]
  apply encode_length_bound
  intro x hx
  obtain ⟨i,hi,hm⟩ := List.mem_flatMap.mp hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
  exact hW i j (List.mem_range.mp hi) (List.mem_range.mp hj)
lemma query_length_bound (n W : ℕ) (entry : ℕ → ℕ → BitString)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W) :
    (queryBits n entry).length ≤ 2*n+n*n*(2*W+2)+1 := by
  have hh := data_length_bound n W entry hW
  simp only [queryBits,pairBits_length,List.length_replicate]
  omega
lemma query_reverse (n : ℕ) (entry : ℕ → ℕ → BitString) :
    (queryBits n entry).reverse=(encodeBitList (matrixWords n entry)).reverse++false::List.replicate (2*n) true := by
  rw [queryBits,MatrixEmitter.pairBits_append,unary_header]
  simp [List.reverse_append]

noncomputable def block (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  seq headerBlock (seq copyOuter (seq (rowsLoop B) finishBlock))
noncomputable def arrayBlock (B : OracleBlock (k+7)) : OracleBlock (k+7) :=
  seq copyOuter (seq (rowsLoop B) finishBlock)

theorem block_executes (B : OracleBlock (k+7)) (entry : ℕ → ℕ → BitString)
    (n T W : ℕ) (params : Store (k+7))
    (hB : ∀g i j out inner outer,i<n → j<n → ∃c,
      B.Executes g (store n i j [] out inner outer params) (store n i j (entry i j) out inner outer params) c ∧ c ≤ T)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W) (g : BitString → ℕ) :
    ∃c,(block B).Executes g (store n 0 0 [] [] [] [] params)
      (Function.update (store n 0 0 [] [] [] [] params) (port 7) (queryBits n entry)) c ∧
      c ≤ n*n*(T+10*W+24)+40*n+30 := by
  let pre : BitString := false::List.replicate (2*n) true
  obtain ⟨c,hc,hcb⟩ := rows_loop B entry n T W params hB hW g 0 n pre (by omega)
  have hrows := whilePop_executes _ _ _ g hc
  have he : rowsOutput entry n 0 n pre=(queryBits n entry).reverse := by
    rw [rowsOutput_eq,←List.range_eq_range']
    exact (query_reverse n entry).symm
  simp only [Nat.zero_add,he] at hrows
  have hf := finishBlock_executes g n n (queryBits n entry).reverse params
  simp only [List.reverse_reverse,List.length_reverse] at hf
  have hh := seq_executes _ _ g (headerBlock_executes g n params)
    (seq_executes _ _ g (copyOuter_executes g n 0 0 [] pre [] params)
      (seq_executes _ _ g hrows hf))
  refine ⟨_,hh,?_⟩
  have hl := query_length_bound n W entry hW
  nlinarith

theorem arrayBlock_executes (B : OracleBlock (k+7)) (entry : ℕ → ℕ → BitString)
    (n T W : ℕ) (params : Store (k+7))
    (hB : ∀g i j out inner outer,i<n → j<n → ∃c,
      B.Executes g (store n i j [] out inner outer params) (store n i j (entry i j) out inner outer params) c ∧ c ≤ T)
    (hW : ∀i j,i<n → j<n → (entry i j).length ≤ W) (g : BitString → ℕ) :
    ∃c,(arrayBlock B).Executes g (store n 0 0 [] [] [] [] params)
      (Function.update (store n 0 0 [] [] [] [] params) (port 7) (encodeBitList (matrixWords n entry))) c ∧
      c ≤ n*n*(T+10*W+24)+40*n+30 := by
  obtain ⟨c,hc,hcb⟩ := rows_loop B entry n T W params hB hW g 0 n [] (by omega)
  have hrows := whilePop_executes _ _ _ g hc
  have he : rowsOutput entry n 0 n []=(encodeBitList (matrixWords n entry)).reverse := by
    simp [rowsOutput_eq,←List.range_eq_range',matrixWords]
  simp only [Nat.zero_add,he] at hrows
  have hf := finishBlock_executes g n n (encodeBitList (matrixWords n entry)).reverse params
  simp only [List.reverse_reverse,List.length_reverse] at hf
  have hh := seq_executes _ _ g (copyOuter_executes g n 0 0 [] [] [] params) (seq_executes _ _ g hrows hf)
  refine ⟨_,hh,?_⟩
  have hl := data_length_bound n W entry hW
  nlinarith

lemma rowsLoop_queryFree (B : OracleBlock (k+7)) (hB : B.QueryFree) : (rowsLoop B).QueryFree := by
  have he : (emitWord (k:=k)).QueryFree := HiddenCircuits.Approximation.SelfReduction.Runtime.emitWordReversed_queryFree _ _
  have hentry : (entryBody B).QueryFree := seq_queryFree _ _ hB (seq_queryFree _ _ he (push_queryFree _ _))
  have hrow : (rowLoop B).QueryFree := whilePop_queryFree _ _ _ hentry hentry
  have hbody : (rowsBody B).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ hrow (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
  exact whilePop_queryFree _ _ _ hbody hbody
lemma arrayBlock_queryFree (B : OracleBlock (k+7)) (hB : B.QueryFree) : (arrayBlock B).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (rowsLoop_queryFree B hB)
    (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))
lemma block_queryFree (B : OracleBlock (k+7)) (hB : B.QueryFree) : (block B).QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (CNFEmitter.header_queryFree _ _))
    (arrayBlock_queryFree B hB)
end HiddenCircuits.Approximation.Initialization.WordMatrixEmitter
