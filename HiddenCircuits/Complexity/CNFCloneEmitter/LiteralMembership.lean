import HiddenCircuits.Complexity.CNFCloneEmitter.WordEquality
import HiddenCircuits.Complexity.CNFCloneEmitter.ClauseLookup

/-! Actual literal membership over a canonical encoded word list. Parsed words
are compared by the real linear bit comparator; the target word is preserved. -/
namespace HiddenCircuits.Complexity.CNFCloneEmitter.LiteralMembership
open OracleBlock
open BinaryArithmetic (pair_parse_cost)

def store (stream target : BitString) (found : Bool) (word temporary flag copy work : BitString) : Store 7 := fun i =>
  if i.val=0 then stream else if i.val=1 then target else if i.val=2 then [found]
  else if i.val=3 then word else if i.val=4 then temporary else if i.val=5 then flag
  else if i.val=6 then copy else work

def parseEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 3 else if i.val=2 then 4 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
def equalEmbedding : Fin 3 ↪ Fin 8 where
  toFun i := if i.val=0 then 3 else if i.val=1 then 6 else 5
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def parse : OracleBlock 7 := GraphVerifier.Runtime.unpairOn parseEmbedding
noncomputable def compare : OracleBlock 7 := rename WordEquality.program equalEmbedding
noncomputable def setTrue : OracleBlock 7 := seq (clear 2) (push 2 true)
noncomputable def accumulate : OracleBlock 7 := branchPop 5 skip skip setTrue
noncomputable def body : OracleBlock 7 := seq parse
  (seq (copyOn 1 6 7 (by decide) (by decide) (by decide)) (seq compare accumulate))
noncomputable def program : OracleBlock 7 := whilePop 0 body body

theorem parse_executes (g : BitString → ℕ) (word rest target : BitString) (found : Bool) :
    parse.Executes g (store (pairBits word rest) target found [] [] [] [] [])
      (store rest target found word [] [true] [] []) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes parseEmbedding g
    (store (pairBits word rest) target found [] [] [] [] [])
    (store rest target found word [] [true] [] []) (pairBits word rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim)
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

theorem compare_executes (g : BitString → ℕ) (rest target word : BitString) (found : Bool) :
    ∃ cost, compare.Executes g (store rest target found word [] [true] target [])
      (store rest target found [] [] [decide (word=target)] [] []) cost ∧ cost≤10*(word.length+target.length)+13 := by
  obtain ⟨c,hc,hb⟩ := WordEquality.program_executes g word target
  refine ⟨c,?_,hb⟩
  apply rename_executes_to _ equalEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim

theorem setTrue_executes (g : BitString → ℕ) (rest target : BitString) (found : Bool) :
    setTrue.Executes g (store rest target found [] [] [] [] []) (store rest target true [] [] [] [] []) 5 := by
  have hc := clear_executes g (2 : Fin 8) (store rest target found [] [] [] [] [])
  have hp := push_executes g (2 : Fin 8) true (Function.update (store rest target found [] [] [] [] []) 2 [])
  convert seq_executes _ _ g hc hp using 1
  funext i;fin_cases i <;> simp [store]

lemma pop_flag (rest target : BitString) (found bit : Bool) :
    Function.update (store rest target found [] [] [bit] [] []) 5 []=store rest target found [] [] [] [] [] := by
  funext i;fin_cases i <;> rfl

theorem accumulate_executes (g : BitString → ℕ) (rest target : BitString) (found bit : Bool) :
    ∃ cost, accumulate.Executes g (store rest target found [] [] [bit] [] [])
      (store rest target (found || bit) [] [] [] [] []) cost ∧ cost≤7 := by
  cases bit
  · refine ⟨3,?_,by omega⟩
    apply branchPop_false _ _ _ _ g rfl
    simpa only [pop_flag,Bool.or_false] using skip_executes g (store rest target found [] [] [] [] [])
  · refine ⟨7,?_,by omega⟩
    apply branchPop_true _ _ _ _ g rfl
    simpa only [pop_flag,Bool.or_true] using setTrue_executes g rest target found

theorem body_executes (g : BitString → ℕ) (word rest target : BitString) (found : Bool) :
    ∃ cost, body.Executes g (store (pairBits word rest) target found [] [] [] [] [])
      (store rest target (found || decide (word=target)) [] [] [] [] []) cost ∧
      cost≤15*word.length+15*target.length+31 := by
  have hp := parse_executes g word rest target found
  have hcopy : (copyOn (1 : Fin 8) 6 7 (by decide) (by decide) (by decide)).Executes g
      (store rest target found word [] [true] [] []) (store rest target found word [] [true] target []) (5*target.length+2) := by
    convert copyOn_executes g (1 : Fin 8) 6 7 (by decide) (by decide) (by decide)
      (store rest target found word [] [true] [] []) rfl using 1
    funext i;fin_cases i <;> simp [store]
  obtain ⟨ce,he,hbe⟩ := compare_executes g rest target word found
  obtain ⟨ca,ha,hba⟩ := accumulate_executes g rest target found (decide (word=target))
  refine ⟨5*word.length+3+((5*target.length+2)+(ce+ca+2)+2)+2,
    seq_executes _ _ g hp (seq_executes _ _ g hcopy (seq_executes _ _ g he ha)),?_⟩
  omega

lemma pop_stream (word rest target : BitString) (found : Bool) :
    Function.update (store (true::pairBits word rest) target found [] [] [] [] []) 0 (pairBits word rest)=
      store (pairBits word rest) target found [] [] [] [] [] := by
  funext i;fin_cases i <;> rfl

theorem loop_execution (g : BitString → ℕ) (ws : List BitString) (target : BitString) (found : Bool) :
    ∃ cost, WhileExecution (0 : Fin 8) body body g (store (encodeBitList ws) target found [] [] [] [] [])
      (store [] target (found || decide (target∈ws)) [] [] [] [] []) cost ∧
      cost≤15*(ws.map List.length).sum+ws.length*(15*target.length+33)+1 := by
  induction ws generalizing found with
  | nil => exact ⟨1,by simpa [encodeBitList] using WhileExecution.empty (store [] target found [] [] [] [] []) rfl,by simp⟩
  | cons w ws ih =>
    obtain ⟨cb,hb,hbb⟩ := body_executes g w (encodeBitList ws) target found
    obtain ⟨ct,ht,hbt⟩ := ih (found || decide (w=target))
    have hbody : body.Executes g
        (Function.update (store (encodeBitList (w::ws)) target found [] [] [] [] []) 0 (pairBits w (encodeBitList ws)))
        (store (encodeBitList ws) target (found || decide (w=target)) [] [] [] [] []) cb := by
      rw [encodeBitList,pop_stream];exact hb
    have h := WhileExecution.one
      (stack:=(0:Fin 8)) (B:=body) (C:=body) (g:=g)
      (show store (encodeBitList (w::ws)) target found [] [] [] [] [] 0=true::pairBits w (encodeBitList ws) from rfl)
      hbody ht
    refine ⟨1+cb+1+ct,?_,?_⟩
    · simpa only [List.mem_cons,Bool.decide_or,Bool.or_assoc,eq_comm] using h
    · simp only [List.map_cons,List.sum_cons,List.length_cons];nlinarith

/-- Canonical word-list membership, with no assumption about operand equality
cost and no unproved runtime certificate. -/
theorem program_executes (g : BitString → ℕ) (ws : List BitString) (target : BitString) :
    ∃ cost, program.Executes g (store (encodeBitList ws) target false [] [] [] [] [])
      (store [] target (decide (target∈ws)) [] [] [] [] []) cost ∧
      cost≤40*((encodeBitList ws).length+target.length+1)^2 := by
  obtain ⟨c,hc,hb⟩ := loop_execution g ws target false
  refine ⟨c,?_,?_⟩
  · simpa only [Bool.false_or] using whilePop_executes _ _ _ g hc
  · have he := encodeBitList_length ws
    have hl : ws.length≤(encodeBitList ws).length := list_length_le_encodeBitList_length ws
    have hs : (ws.map List.length).sum≤(encodeBitList ws).length := by omega
    have hm := Nat.mul_le_mul_right (15*target.length+33) hl
    nlinarith [sq_nonneg ((encodeBitList ws).length : ℤ)]

lemma parse_queryFree : parse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
lemma compare_queryFree : compare.QueryFree := rename_queryFree _ _ WordEquality.program_queryFree
lemma setTrue_queryFree : setTrue.QueryFree := seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)
lemma accumulate_queryFree : accumulate.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree setTrue_queryFree
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ parse_queryFree
  (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ compare_queryFree accumulate_queryFree))
lemma program_queryFree : program.QueryFree := whilePop_queryFree _ _ _ body_queryFree body_queryFree

end HiddenCircuits.Complexity.CNFCloneEmitter.LiteralMembership
