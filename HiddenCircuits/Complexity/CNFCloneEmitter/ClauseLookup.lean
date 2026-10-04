import HiddenCircuits.Complexity.CNFCloneEmitter.Dimensions

/-! Actual indexed extraction from a canonical self-delimiting word list. The
index is a unary clock; each skipped word is parsed and physically discarded. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup
open OracleBlock
open BinaryArithmetic (pair_parse_cost)

def store (data index output temporary flag : BitString) : Store 4 := fun i =>
  if i.val=0 then data else if i.val=1 then index else if i.val=2 then output else if i.val=3 then temporary else flag

def parseEmbedding : Fin 4 ↪ Fin 5 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 2 else if i.val=2 then 3 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def parseOne : OracleBlock 4 := GraphVerifier.Runtime.unpairOn parseEmbedding
noncomputable def skipBody : OracleBlock 4 := seq parseOne (seq (clear 2) (clear 4))
noncomputable def skipOne : OracleBlock 4 := branchPop 0 skip skipBody skipBody
noncomputable def skipLoop : OracleBlock 4 := whilePop 1 skipOne skipOne
noncomputable def takeBody : OracleBlock 4 := seq parseOne (seq (clear 4) (clear 0))
noncomputable def takeOne : OracleBlock 4 := branchPop 0 skip takeBody takeBody
noncomputable def program : OracleBlock 4 := seq skipLoop takeOne

theorem parseOne_executes (g : BitString → ℕ) (index word rest : BitString) :
    parseOne.Executes g (store (pairBits word rest) index [] [] [])
      (store rest index word [] [true]) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes parseEmbedding g
    (store (pairBits word rest) index [] [] []) (store rest index word [] [true]) (pairBits word rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim)
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

theorem skipBody_executes (g : BitString → ℕ) (index word rest : BitString) :
    skipBody.Executes g (store (pairBits word rest) index [] [] [])
      (store rest index [] [] []) (6*word.length+10) := by
  have h1 : (clear (2 : Fin 5)).Executes g (store rest index word [] [true])
      (store rest index [] [] [true]) (word.length+1) := by
    convert clear_executes g (2 : Fin 5) (store rest index word [] [true]) using 1
    funext i;fin_cases i <;> simp [store]
  have h2 : (clear (4 : Fin 5)).Executes g (store rest index [] [] [true])
      (store rest index [] [] []) 2 := by
    convert clear_executes g (4 : Fin 5) (store rest index [] [] [true]) using 1
    funext i;fin_cases i <;> simp [store]
  convert seq_executes _ _ g (parseOne_executes g index word rest) (seq_executes _ _ g h1 h2) using 1 <;> omega

lemma pop_data (data index : BitString) (b : Bool) :
    Function.update (store (b::data) index [] [] []) 0 data=store data index [] [] [] := by
  funext i;fin_cases i <;> rfl
lemma pop_index (data index : BitString) (b : Bool) :
    Function.update (store data (b::index) [] [] []) 1 index=store data index [] [] [] := by
  funext i;fin_cases i <;> rfl

theorem skipOne_cons (g : BitString → ℕ) (index word : BitString) (words : List BitString) :
    skipOne.Executes g (store (encodeBitList (word::words)) index [] [] [])
      (store (encodeBitList words) index [] [] []) (6*word.length+12) := by
  convert branchPop_true 0 skip skipBody skipBody g rfl
    (s:=store (encodeBitList (word::words)) index [] [] [])
    (by rw [encodeBitList,pop_data];exact skipBody_executes g index word (encodeBitList words)) using 1 <;> omega

theorem skipOne_nil (g : BitString → ℕ) (index : BitString) :
    skipOne.Executes g (store [] index [] [] []) (store [] index [] [] []) 3 :=
  branchPop_empty 0 skip skipBody skipBody g rfl (by simpa using skip_executes g (store [] index [] [] []))

lemma encode_tail_length (w : BitString) (ws : List BitString) :
    (encodeBitList ws).length≤(encodeBitList (w::ws)).length := by simp [encodeBitList];omega
lemma encode_drop_length (ws : List BitString) (j : ℕ) :
    (encodeBitList (ws.drop j)).length≤(encodeBitList ws).length := by
  induction j generalizing ws with
  | zero => simp
  | succ j ih =>
    cases ws with
    | nil => simp
    | cons w ws => exact (ih ws).trans (encode_tail_length w ws)

theorem skipLoop_execution (g : BitString → ℕ) (ws : List BitString) (j : ℕ) :
    ∃ cost, WhileExecution (1 : Fin 5) skipOne skipOne g
      (store (encodeBitList ws) (List.replicate j true) [] [] [])
      (store (encodeBitList (ws.drop j)) [] [] [] []) cost ∧
      cost≤j*(6*(encodeBitList ws).length+14)+1 := by
  induction j generalizing ws with
  | zero => exact ⟨1,by simpa using WhileExecution.empty (store (encodeBitList ws) [] [] [] []) rfl,by simp⟩
  | succ j ih =>
    cases ws with
    | nil =>
      obtain ⟨ct,ht,hbt⟩ := ih []
      have hb := skipOne_nil g (List.replicate j true)
      have h : WhileExecution (1 : Fin 5) skipOne skipOne g
          (store [] (List.replicate (j+1) true) [] [] []) (store [] [] [] [] []) (1+3+1+ct) := by
        apply WhileExecution.one rfl
        · simpa only [List.replicate_succ,pop_index] using hb
        · simpa using ht
      exact ⟨_,by simpa [encodeBitList] using h,by simp [encodeBitList] at hbt ⊢;omega⟩
    | cons w ws =>
      obtain ⟨ct,ht,hbt⟩ := ih ws
      have hb := skipOne_cons g (List.replicate j true) w ws
      have h : WhileExecution (1 : Fin 5) skipOne skipOne g
          (store (encodeBitList (w::ws)) (List.replicate (j+1) true) [] [] [])
          (store (encodeBitList (ws.drop j)) [] [] [] []) (1+(6*w.length+12)+1+ct) := by
        apply WhileExecution.one rfl
        · simpa only [List.replicate_succ,pop_index] using hb
        · exact ht
      refine ⟨_,by simpa only [List.drop_succ_cons] using h,?_⟩
      have hm := Nat.mul_le_mul_left j (show 6*(encodeBitList ws).length+14≤6*(encodeBitList (w::ws)).length+14 by
        have := encode_tail_length w ws;omega)
      have hw : w.length≤(encodeBitList (w::ws)).length := by simp [encodeBitList];omega
      nlinarith

theorem takeBody_executes (g : BitString → ℕ) (word rest : BitString) :
    takeBody.Executes g (store (pairBits word rest) [] [] [] [])
      (store [] [] word [] []) (5*word.length+rest.length+10) := by
  have h1 : (clear (4 : Fin 5)).Executes g (store rest [] word [] [true])
      (store rest [] word [] []) 2 := by
    convert clear_executes g (4 : Fin 5) (store rest [] word [] [true]) using 1
    funext i;fin_cases i <;> simp [store]
  have h2 : (clear (0 : Fin 5)).Executes g (store rest [] word [] [])
      (store [] [] word [] []) (rest.length+1) := by
    convert clear_executes g (0 : Fin 5) (store rest [] word [] []) using 1
    funext i;fin_cases i <;> simp [store]
  convert seq_executes _ _ g (parseOne_executes g [] word rest) (seq_executes _ _ g h1 h2) using 1 <;> omega

theorem takeOne_executes (g : BitString → ℕ) (ws : List BitString) :
    ∃ cost, takeOne.Executes g (store (encodeBitList ws) [] [] [] [])
      (store [] [] (ws.head?.getD []) [] []) cost ∧ cost≤6*(encodeBitList ws).length+12 := by
  cases ws with
  | nil => exact ⟨3,branchPop_empty 0 skip takeBody takeBody g rfl (by simpa using skip_executes g (store [] [] [] [] [])),by simp⟩
  | cons w ws =>
    have h := branchPop_true 0 skip takeBody takeBody g rfl
      (s:=store (encodeBitList (w::ws)) [] [] [] [])
      (by rw [encodeBitList,pop_data];exact takeBody_executes g w (encodeBitList ws))
    refine ⟨_,h,?_⟩
    simp [encodeBitList];omega

/-- A total-on-canonical-lists indexed read: out-of-range indices return the
empty word, and every parser/counter stack is physically cleared. -/
theorem program_executes (g : BitString → ℕ) (ws : List BitString) (j : ℕ) :
    ∃ cost, program.Executes g (store (encodeBitList ws) (List.replicate j true) [] [] [])
      (store [] [] (ws[j]?.getD []) [] []) cost ∧
      cost≤(j+1)*(6*(encodeBitList ws).length+14)+1 := by
  obtain ⟨cl,hl,hbl⟩ := skipLoop_execution g ws j
  obtain ⟨ct,ht,hbt⟩ := takeOne_executes g (ws.drop j)
  have h := seq_executes _ _ g (whilePop_executes _ _ _ g hl) ht
  refine ⟨cl+ct+2,?_,?_⟩
  · simpa only [List.head?_drop] using h
  · have hd := encode_drop_length ws j;nlinarith

lemma parseOne_queryFree : parseOne.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
lemma skipBody_queryFree : skipBody.QueryFree := seq_queryFree _ _ parseOne_queryFree (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))
lemma skipOne_queryFree : skipOne.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skipBody_queryFree skipBody_queryFree
lemma skipLoop_queryFree : skipLoop.QueryFree := whilePop_queryFree _ _ _ skipOne_queryFree skipOne_queryFree
lemma takeBody_queryFree : takeBody.QueryFree := seq_queryFree _ _ parseOne_queryFree (seq_queryFree _ _ (clear_queryFree _) (clear_queryFree _))
lemma takeOne_queryFree : takeOne.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree takeBody_queryFree takeBody_queryFree
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ skipLoop_queryFree takeOne_queryFree

end HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup
