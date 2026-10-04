import HiddenCircuits.GraphReduction.Runtime.RankEmitterRows

namespace HiddenCircuits.GraphReduction.Runtime.RankEmitter
open Complexity OracleBlock MatrixEmitter BinaryArithmetic
variable {k : ℕ}
set_option maxHeartbeats 800000

def words (n : ℕ) (edge : ℕ→ℕ→Bool) : List BitString := (List.range n).map (fun i=>List.replicate (rowCount edge i 0 n) true)
def bits (n : ℕ) (edge : ℕ→ℕ→Bool) : BitString := encodeBitList (words n edge)

lemma rowsOutput_eq (edge : ℕ→ℕ→Bool) (n i m : ℕ) (out : BitString) :
    rowsOutput edge n i m out=((List.range' i m).flatMap (rowWord edge n)).reverse++out := by
  induction m generalizing i out with
  | zero => simp [rowsOutput]
  | succ m ih => simp [rowsOutput,ih,List.range'_succ,List.reverse_append,List.append_assoc]

lemma rowsOutput_full (edge : ℕ→ℕ→Bool) (n : ℕ) : rowsOutput edge n 0 n []=(bits n edge).reverse := by
  rw [rowsOutput_eq,←List.range_eq_range']
  simp only [bits,words,encodeBitList_eq_chunks,List.flatMap_map,List.append_nil,rowWord,Function.comp_def]
  rfl

lemma encodedUnary_length_bound (xs : List ℕ) (B : ℕ) (hB : ∀x∈xs,x≤B) :
    (encodeBitList (xs.map (fun x=>List.replicate x true))).length≤xs.length*(2*B+2) := by
  induction xs with
  | nil => simp [encodeBitList]
  | cons x xs ih =>
    have hx:=hB x (by simp)
    have ht:=ih (fun y hy=>hB y (by simp [hy]))
    simp only [List.map_cons,encodeBitList,List.length_cons,pairBits_length,List.length_replicate]
    nlinarith

lemma bits_length_bound (n : ℕ) (edge : ℕ→ℕ→Bool) : (bits n edge).length≤2*n*n+2*n := by
  have h:=encodedUnary_length_bound ((List.range n).map (fun i=>rowCount edge i 0 n)) n (by
    intro x hx
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hx
    exact rowCount_le edge i 0 n)
  simp only [List.map_map,List.length_map,List.length_range,Function.comp_def] at h
  simpa only [bits,words,show n*(2*n+2)=2*n*n+2*n by ring] using h

noncomputable def block (B : OracleBlock (k+7)) : OracleBlock (k+7) := seq copyOuter (seq (rowsLoop B) finishBlock)

theorem block_executes (B : OracleBlock (k+7)) (edge : ℕ→ℕ→Bool) (n T : ℕ) (params : Store (k+7))
    (hB : ∀g i j out inner outer,i<n→j<n→∃c,B.Executes g (store n i j [] out inner outer params)
      (store n i j [edge i j] out inner outer params) c ∧ c≤T)
    (g : BitString→ℕ) :
    ∃c,(block B).Executes g (store n 0 0 [] [] [] [] params)
      (Function.update (store n 0 0 [] [] [] [] params) (port 7) (bits n edge)) c ∧
      c≤n*n*(T+30)+40*n+20 := by
  obtain ⟨c,hc,hb⟩:=rows_loop B edge n T params hB g 0 n [] (by omega)
  have hr:=whilePop_executes _ _ _ g hc
  simp only [Nat.zero_add,rowsOutput_full] at hr
  have hf:=finishBlock_executes g n n (bits n edge).reverse params
  simp only [List.reverse_reverse,List.length_reverse] at hf
  have hh:=seq_executes _ _ g (copyOuter_executes g n 0 0 [] [] [] params) (seq_executes _ _ g hr hf)
  refine ⟨5*n+2+(c+(n+2*(bits n edge).length+4)+2)+2,hh,?_⟩
  have hl:=bits_length_bound n edge
  nlinarith

lemma block_queryFree (B : OracleBlock (k+7)) (hB:B.QueryFree) : (block B).QueryFree := by
  have he : (emitCount (k:=k)).QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
  have hi : (entry B).QueryFree := seq_queryFree _ _ hB (seq_queryFree _ _ he (push_queryFree _ _))
  have hl : (rowLoop B).QueryFree := whilePop_queryFree _ _ _ hi hi
  have hb : (rowsBody B).QueryFree := seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ hl (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)))))
  exact seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (whilePop_queryFree _ _ _ hb hb)
    (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _)))
end HiddenCircuits.GraphReduction.Runtime.RankEmitter
