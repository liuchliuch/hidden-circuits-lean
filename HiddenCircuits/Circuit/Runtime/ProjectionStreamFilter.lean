import HiddenCircuits.Circuit.Runtime.ProjectionStreamPure

namespace HiddenCircuits.Circuit.Runtime.ProjectionStream
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic LetterEmitter

def store (n p b r : ℕ) (out exponent : BitString) : Store 10 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then out else if i.val=2 then exponent
  else if i.val=3 then List.replicate p true else if i.val=4 then List.replicate b true
  else if i.val=5 then List.replicate r true else []
def atomEmbedding : Fin 4 ↪ Fin 11 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 1 else if i.val=2 then 6 else 7
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def filterBody : OracleBlock 10 :=
  seq (fixedWordOn atomEmbedding filterWord)
    (seq (prepend 3 (List.replicate 4 true)) (prepend 2 (List.replicate 6 true)))

theorem filterBody_executes (oracle : BitString → ℕ) (n p b r : ℕ) (out exponent : BitString) :
    filterBody.Executes oracle (store n p b r out exponent)
      (store n (p+4) b r ((wordBitsAt p filterWord).reverse++out) (List.replicate 6 true++exponent))
      (wordCost p filterWord+36) := by
  have he : (fixedWordOn atomEmbedding filterWord).Executes oracle (store n p b r out exponent)
      (store n p b r ((wordBitsAt p filterWord).reverse++out) exponent) (wordCost p filterWord) := by
    convert fixedWordOn_executes atomEmbedding oracle (store n p b r out exponent) filterWord p
      (by funext i;fin_cases i <;> rfl) using 1
    funext i;fin_cases i <;> simp [store,atomEmbedding]
  have hp : (prepend (3:Fin 11) (List.replicate 4 true)).Executes oracle
      (store n p b r ((wordBitsAt p filterWord).reverse++out) exponent)
      (store n (p+4) b r ((wordBitsAt p filterWord).reverse++out) exponent) 13 := by
    convert prepend_executes oracle (3:Fin 11) (List.replicate 4 true)
      (store n p b r ((wordBitsAt p filterWord).reverse++out) exponent) using 1
    funext i;fin_cases i <;> simp [store,List.replicate_succ]
  have hq : (prepend (2:Fin 11) (List.replicate 6 true)).Executes oracle
      (store n (p+4) b r ((wordBitsAt p filterWord).reverse++out) exponent)
      (store n (p+4) b r ((wordBitsAt p filterWord).reverse++out) (List.replicate 6 true++exponent)) 19 := by
    convert prepend_executes oracle (2:Fin 11) (List.replicate 6 true)
      (store n (p+4) b r ((wordBitsAt p filterWord).reverse++out) exponent) using 1
    funext i;fin_cases i <;> simp [store]
  exact seq_executes _ _ oracle he (seq_executes _ _ oracle hp hq)

theorem filterBody_cost (p : ℕ) : wordCost p filterWord+36≤3000*(p+1) := by
  have hh := wordCost_bound p filterWord
  rw [filterWord_length] at hh
  nlinarith

noncomputable def filterLoop : OracleBlock 10 := whilePop 4 filterBody filterBody

theorem filterLoop_execution (oracle : BitString → ℕ) (b n p r : ℕ) (out exponent : BitString) :
    ∃t, WhileExecution (4:Fin 11) filterBody filterBody oracle (store n p b r out exponent)
      (store n (p+4*b) 0 r ((filterStream p b).reverse++out) (List.replicate (6*b) true++exponent)) t ∧
      t≤b*(3000*(p+4*b+1)+2)+1 := by
  induction b generalizing p out exponent with
  | zero =>
    refine ⟨1,?_,by omega⟩
    simpa [filterStream] using (WhileExecution.empty (stack:=(4:Fin 11)) (B:=filterBody) (C:=filterBody) (g:=oracle)
      (store n p 0 r out exponent) rfl)
  | succ b ih =>
    have hc := filterBody_executes oracle n p b r out exponent
    have hs : Function.update (store n p (b+1) r out exponent) (4:Fin 11) (List.replicate b true)=store n p b r out exponent := by
      funext i;fin_cases i <;> simp [store]
    rw [←hs] at hc
    obtain ⟨t,ht,htb⟩ := ih (p+4) ((wordBitsAt p filterWord).reverse++out) (List.replicate 6 true++exponent)
    have hh := WhileExecution.one (stack:=(4:Fin 11))
      (show store n p (b+1) r out exponent 4=true::List.replicate b true from rfl) hc ht
    refine ⟨1+(wordCost p filterWord+36)+1+t,?_,?_⟩
    · convert hh using 1
      simp only [filterStream,List.reverse_append,←List.append_assoc,←List.replicate_add,
        show p+4+4*b=p+4*(b+1) by omega,show 6*b+6=6*(b+1) by omega]
    · have hb := filterBody_cost p
      nlinarith

theorem filterLoop_executes (oracle : BitString → ℕ) (b n p r : ℕ) (out exponent : BitString) :
    ∃t, filterLoop.Executes oracle (store n p b r out exponent)
      (store n (p+4*b) 0 r ((filterStream p b).reverse++out) (List.replicate (6*b) true++exponent)) t ∧
      t≤b*(3000*(p+4*b+1)+2)+1 := by
  obtain ⟨t,ht,hb⟩ := filterLoop_execution oracle b n p r out exponent
  exact ⟨t,whilePop_executes _ _ _ _ ht,hb⟩

theorem filterBody_queryFree : filterBody.QueryFree := seq_queryFree _ _ (fixedWordOn_queryFree _ _)
  (seq_queryFree _ _ (prepend_queryFree _ _) (prepend_queryFree _ _))
theorem filterLoop_queryFree : filterLoop.QueryFree := whilePop_queryFree _ _ _ filterBody_queryFree filterBody_queryFree
end HiddenCircuits.Circuit.Runtime.ProjectionStream
