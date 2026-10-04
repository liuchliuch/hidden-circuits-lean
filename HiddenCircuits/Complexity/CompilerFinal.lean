import HiddenCircuits.Complexity.CompilerState
import HiddenCircuits.Complexity.UniformSerialization

/-! Actual final accepting-clause emission and stream reversal for the uniform
verifier compiler. Address arithmetic and every copied/pushed bit are charged. -/
namespace HiddenCircuits.Complexity.CompilerState
open OracleBlock Polynomial

def indexEmbedding : Fin 5 ↪ Fin 18 where
  toFun i := ⟨i.val,by have := i.isLt;omega⟩
  inj' := by intro i j h;exact Fin.ext (congrArg (fun q : Fin 18 => q.val) h)

noncomputable def acceptIndex (offset : ℕ) : OracleBlock 17 :=
  rename (UnaryIndex.build 0 0 0 offset) indexEmbedding

theorem acceptIndex_executes (g : BitString → ℕ) (offset : ℕ) (x : BitString) (R : Registers) (hs : R.source=0) :
    ∃ cost, (acceptIndex offset).Executes g (store x R)
      (Function.update (store x R) 2 (List.replicate (R.base+offset) true)) cost ∧ cost ≤ 5*R.base+3*offset+20 := by
  obtain ⟨cost,hc,hb⟩ := UnaryIndex.build_executes g 0 0 0 offset 0 R.base
  refine ⟨cost,?_,by simpa using hb⟩
  apply rename_executes_to _ indexEmbedding g hc
  · funext i;fin_cases i <;> simp [store,UnaryIndex.state,hs,indexEmbedding]
  · funext i;fin_cases i <;> simp [store,UnaryIndex.state,hs,indexEmbedding]
  · intro i hi
    exact Function.update_of_ne (fun h => hi 2 h.symm) _ _

lemma indexedLiteral_executes (g : BitString → ℕ) (x : BitString) (R : Registers) (index : ℕ) (sign : Bool) :
    (CNFEmitter.literal (2 : Fin 18) 6 sign).Executes g
      (Function.update (store x R) 2 (List.replicate index true))
      (store x {R with stream:=(serializedLiteral index sign).reverse++R.stream}) (27*index+43) := by
  have h := CNFEmitter.literal_executes g (2 : Fin 18) 6 (by decide) sign
    (Function.update (store x R) 2 (List.replicate index true))
  convert h using 1
  · funext i;fin_cases i <;> simp [store]
  · simp

noncomputable def accept (offset : ℕ) : OracleBlock 17 :=
  seq (push 6 true) (seq (acceptIndex offset) (seq (CNFEmitter.literal 2 6 true) (push 6 false)))
noncomputable def acceptTime (offset : ℕ) : Polynomial ℕ := 32*X+C (30*offset+71)

theorem accept_executes (g : BitString → ℕ) (offset : ℕ) (x : BitString) (R : Registers) (hs : R.source=0) :
    ∃ cost, (accept offset).Executes g (store x R)
      (store x {R with stream:=(serializedClause [(R.base+offset,true)]).reverse++R.stream}) cost ∧
      cost ≤ (acceptTime offset).eval R.base := by
  let R₁ := {R with stream:=true::R.stream}
  have h₁ : (push (6 : Fin 18) true).Executes g (store x R) (store x R₁) 1 := by
    simpa only [update_stream] using push_executes g (6 : Fin 18) true (store x R)
  obtain ⟨ci,hi,hbi⟩ := acceptIndex_executes g offset x R₁ hs
  have h₂ := indexedLiteral_executes g x R₁ (R.base+offset) true
  let R₂ := {R₁ with stream:=(serializedLiteral (R.base+offset) true).reverse++R₁.stream}
  have h₃ : (push (6 : Fin 18) false).Executes g (store x R₂)
      (store x {R with stream:=(serializedClause [(R.base+offset,true)]).reverse++R.stream}) 1 := by
    have h := push_executes g (6 : Fin 18) false (store x R₂)
    simpa [R₂,R₁,update_stream,serializedClause,List.reverse_append,List.append_assoc] using h
  have h := seq_executes _ _ g h₁ (seq_executes _ _ g hi (seq_executes _ _ g h₂ h₃))
  refine ⟨_,h,?_⟩
  simp only [acceptTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat]
  dsimp only [R₁] at hbi
  omega

lemma accept_queryFree (offset : ℕ) : (accept offset).QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (rename_queryFree _ _ (UnaryIndex.build_queryFree _ _ _ _))
    (seq_queryFree _ _ (CNFEmitter.literal_queryFree _ _ _) (push_queryFree _ _)))

noncomputable def finish : OracleBlock 17 := reverseOn 6 0 (by decide)

def finishedStore (x : BitString) (R : Registers) : Store 17 :=
  Function.update (store x {R with stream:=[]}) 0 R.stream.reverse

theorem finish_executes (g : BitString → ℕ) (x : BitString) (R : Registers) (hs : R.source=0) :
    finish.Executes g (store x R) (finishedStore x R) (2*R.stream.length+1) := by
  have h := reverseOn_executes g (6 : Fin 18) 0 (by decide) (store x R)
  simpa [finishedStore,update_stream,store,hs] using h

@[simp] lemma finishedStore_output (x : BitString) (R : Registers) : finishedStore x R 0 = R.stream.reverse := by
  simp [finishedStore]

lemma finish_queryFree : finish.QueryFree := reverseOn_queryFree _ _ _

end HiddenCircuits.Complexity.CompilerState
