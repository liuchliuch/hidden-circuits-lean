import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointState

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 1000000

def wordEmbedding (src dst : Fin 70) (h:src≠dst) : Fin 2 ↪ Fin 70 where
  toFun i:=if i=0 then src else dst
  inj':=by intro i j hij;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def emitWord (src dst : Fin 70) (h:src≠dst) : OracleBlock 69 := rename wordEmit (wordEmbedding src dst h)
lemma emitWord_executes (g : BitString→ℕ) (src dst : Fin 70) (h:src≠dst) (s : Store 69) :
    (emitWord src dst h).Executes g s
      (Function.update (Function.update s src []) dst ((wordChunk (s src)).reverse++s dst)) (6*(s src).length+7) := by
  apply rename_executes_to wordEmit (wordEmbedding src dst h) g (wordEmit_executes g (s src) (s dst))
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> simp [wordEmbedding,h,Ne.symm h,wordEmitStore] <;> rfl
  · intro i hi
    have hs:i≠src:=by intro he;exact hi 0 (by simpa [wordEmbedding] using he.symm)
    have hd:i≠dst:=by intro he;exact hi 1 (by simpa [wordEmbedding] using he.symm)
    simp only [Function.update_of_ne hs,Function.update_of_ne hd]
lemma emitWord_queryFree (src dst : Fin 70) (h:src≠dst) : (emitWord src dst h).QueryFree := rename_queryFree _ _ wordEmit_queryFree

def compareEmbedding : Fin 6 ↪ Fin 70 where
  toFun i:=(![62,63,64,65,66,67] : Fin 6→Fin 70) i
  inj':=by decide +kernel
noncomputable def compareValues : OracleBlock 69 := readOnlyLTOn compareEmbedding
noncomputable def emitNormal : OracleBlock 69 := seq (emitWord 62 59 (by decide)) (emitWord 63 60 (by decide))
noncomputable def emitSwapped : OracleBlock 69 := seq (emitWord 63 59 (by decide)) (emitWord 62 60 (by decide))
noncomputable def emitOrdered : OracleBlock 69 := seq (branchPop 64 skip emitSwapped emitNormal) (push 61 true)
noncomputable def emitPair : OracleBlock 69 := seq compareValues emitOrdered

lemma compareValues_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (u v : ℕ) :
    ∃c,compareValues.Executes g (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true))
      (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true) [decide (u<v)]) c ∧ c≤6*u+14*v+15 := by
  obtain ⟨c,hc,hb⟩:=readOnlyLTOn_executes compareEmbedding g
    (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true)) u v (by funext j;fin_cases j <;> rfl)
  refine ⟨c,?_,hb⟩
  convert hc using 1
  funext j;fin_cases j <;> rfl

lemma emitNormal_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (u v : ℕ) :
    emitNormal.Executes g (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true))
      (state R i k candidates ranks ⟨(wordChunk (List.replicate u true)).reverse++A.lows,(wordChunk (List.replicate v true)).reverse++A.highs,A.count⟩)
      (6*u+6*v+16) := by
  have h₁:(emitWord 62 59 (by decide)).Executes g
      (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true))
      (state R i k candidates ranks {A with lows:=(wordChunk (List.replicate u true)).reverse++A.lows} [] [] (List.replicate v true)) (6*u+7) := by
    convert emitWord_executes g 62 59 (by decide) (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true)) using 1
    · funext j;fin_cases j <;> rfl
    · simp [state,combine,high]
  have h₂:(emitWord 63 60 (by decide)).Executes g
      (state R i k candidates ranks {A with lows:=(wordChunk (List.replicate u true)).reverse++A.lows} [] [] (List.replicate v true))
      (state R i k candidates ranks ⟨(wordChunk (List.replicate u true)).reverse++A.lows,(wordChunk (List.replicate v true)).reverse++A.highs,A.count⟩) (6*v+7) := by
    convert emitWord_executes g 63 60 (by decide) (state R i k candidates ranks {A with lows:=(wordChunk (List.replicate u true)).reverse++A.lows} [] [] (List.replicate v true)) using 1
    · funext j;fin_cases j <;> rfl
    · simp [state,combine,high]
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

lemma emitSwapped_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (u v : ℕ) :
    emitSwapped.Executes g (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true))
      (state R i k candidates ranks ⟨(wordChunk (List.replicate v true)).reverse++A.lows,(wordChunk (List.replicate u true)).reverse++A.highs,A.count⟩)
      (6*u+6*v+16) := by
  have h₁:(emitWord 63 59 (by decide)).Executes g
      (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true))
      (state R i k candidates ranks {A with lows:=(wordChunk (List.replicate v true)).reverse++A.lows} [] (List.replicate u true)) (6*v+7) := by
    convert emitWord_executes g 63 59 (by decide) (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true)) using 1
    · funext j;fin_cases j <;> rfl
    · simp [state,combine,high]
  have h₂:(emitWord 62 60 (by decide)).Executes g
      (state R i k candidates ranks {A with lows:=(wordChunk (List.replicate v true)).reverse++A.lows} [] (List.replicate u true))
      (state R i k candidates ranks ⟨(wordChunk (List.replicate v true)).reverse++A.lows,(wordChunk (List.replicate u true)).reverse++A.highs,A.count⟩) (6*u+7) := by
    convert emitWord_executes g 62 60 (by decide) (state R i k candidates ranks {A with lows:=(wordChunk (List.replicate v true)).reverse++A.lows} [] (List.replicate u true)) using 1
    · funext j;fin_cases j <;> rfl
    · simp [state,combine,high]
  convert seq_executes _ _ g h₁ h₂ using 1 <;> omega

lemma emitOrdered_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (u v : ℕ) :
    emitOrdered.Executes g (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true) [decide (u<v)])
      (state R i k candidates ranks (emitValues A u v)) (6*u+6*v+21) := by
  let mid:Accum:=⟨(wordChunk (List.replicate (min u v) true)).reverse++A.lows,(wordChunk (List.replicate (max u v) true)).reverse++A.highs,A.count⟩
  have hb:(branchPop (64:Fin 70) skip emitSwapped emitNormal).Executes g
      (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true) [decide (u<v)])
      (state R i k candidates ranks mid) (6*u+6*v+18) := by
    have hu:Function.update (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true) [decide (u<v)]) (64:Fin 70) []=
        state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true):=by funext j;fin_cases j <;> rfl
    by_cases h:u<v
    · apply branchPop_true _ _ _ _ g (show (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true) [decide (u<v)]) 64=true::[] by simp [state,combine,high,h])
      rw [hu]
      simpa only [mid,min_eq_left (Nat.le_of_lt h),max_eq_right (Nat.le_of_lt h)] using emitNormal_executes g R i k candidates ranks A u v
    · apply branchPop_false _ _ _ _ g (show (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true) [decide (u<v)]) 64=false::[] by simp [state,combine,high,h])
      rw [hu]
      simpa only [mid,min_eq_right (Nat.le_of_not_gt h),max_eq_left (Nat.le_of_not_gt h)] using emitSwapped_executes g R i k candidates ranks A u v
  have hp:(push (61:Fin 70) true).Executes g (state R i k candidates ranks mid) (state R i k candidates ranks (emitValues A u v)) 1:=by
    convert push_executes g (61:Fin 70) true (state R i k candidates ranks mid) using 1
    funext j;fin_cases j <;> simp [state,combine,high,mid,emitValues,List.replicate_succ]
  convert seq_executes _ _ g hb hp using 1 <;> omega
lemma emitPair_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (u v : ℕ) :
    ∃c,emitPair.Executes g (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true))
      (state R i k candidates ranks (emitValues A u v)) c ∧ c≤12*u+20*v+38 := by
  obtain ⟨c,hc,hb⟩:=compareValues_executes g R i k candidates ranks A u v
  exact ⟨_,seq_executes _ _ g hc (emitOrdered_executes g R i k candidates ranks A u v),by omega⟩
lemma emitPair_queryFree : emitPair.QueryFree := seq_queryFree _ _ (readOnlyLTOn_queryFree _)
  (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree
    (seq_queryFree _ _ (emitWord_queryFree _ _ _) (emitWord_queryFree _ _ _))
    (seq_queryFree _ _ (emitWord_queryFree _ _ _) (emitWord_queryFree _ _ _))) (push_queryFree _ _))
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
