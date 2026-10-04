import HiddenCircuits.GraphReduction.Runtime.ListLookup
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

/-! Literal query-free word-array parsing and acc reconstruction. -/
namespace HiddenCircuits.DH.Runtime.WordArray
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

/-- Public ports are array, unary index, and replacement word. Ports 3–7 are work. -/
def state (data index value clock acc word temporary flag : BitString) : Store 7 := fun i =>
  if i.val=0 then data else if i.val=1 then index else if i.val=2 then value else
  if i.val=3 then clock else if i.val=4 then acc else if i.val=5 then word else
  if i.val=6 then temporary else flag

def store (data index value : BitString) : Store 7 := state data index value [] [] [] [] []

def parseEmbedding : Fin 4 ↪ Fin 8 where
  toFun i := if i.val=0 then 0 else if i.val=1 then 5 else if i.val=2 then 6 else 7
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

def emitEmbedding : Fin 2 ↪ Fin 8 where
  toFun i := if i.val=0 then 5 else 4
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def parse : OracleBlock 7 := GraphVerifier.Runtime.unpairOn parseEmbedding
noncomputable def emit : OracleBlock 7 := rename wordEmit emitEmbedding
noncomputable def skipBody : OracleBlock 7 := seq parse (seq (clear 7) emit)
noncomputable def skipOne : OracleBlock 7 := branchPop 0 skip skipBody skipBody
noncomputable def skipLoop : OracleBlock 7 := whilePop 3 skipOne skipOne

lemma parse_executes (g : BitString → ℕ) (index value clock acc word rest : BitString) :
    parse.Executes g (state (pairBits word rest) index value clock acc [] [] [])
      (state rest index value clock acc word [] [true]) (5*word.length+3) := by
  have h := GraphVerifier.Runtime.unpairOn_executes parseEmbedding g
    (state (pairBits word rest) index value clock acc [] [] [])
    (state rest index value clock acc word [] [true]) (pairBits word rest)
    (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> simp only [GraphVerifier.parse_pair] <;> rfl)
    (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim)
  convert h using 1
  simp [GraphVerifier.parse_pair,pair_parse_cost];omega

lemma emit_executes (g : BitString → ℕ) (data index value clock acc word : BitString) :
    emit.Executes g (state data index value clock acc word [] [])
      (state data index value clock ((wordChunk word).reverse++acc) [] [] []) (6*word.length+7) := by
  apply rename_executes_to wordEmit emitEmbedding g (wordEmit_executes g word acc)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim

lemma skipBody_executes (g : BitString → ℕ) (index value clock acc word rest : BitString) :
    skipBody.Executes g (state (pairBits word rest) index value clock acc [] [] [])
      (state rest index value clock ((wordChunk word).reverse++acc) [] [] []) (11*word.length+16) := by
  have hc : (clear (7 : Fin 8)).Executes g (state rest index value clock acc word [] [true])
      (state rest index value clock acc word [] []) 2 := by
    convert clear_executes g (7 : Fin 8) (state rest index value clock acc word [] [true]) using 1
    funext i;fin_cases i <;> simp [state]
  convert seq_executes _ _ g (parse_executes g index value clock acc word rest)
    (seq_executes _ _ g hc (emit_executes g rest index value clock acc word)) using 1 <;> omega

lemma pop_data (data index value clock acc : BitString) (b : Bool) :
    Function.update (state (b::data) index value clock acc [] [] []) 0 data=
      state data index value clock acc [] [] [] := by
  funext i;fin_cases i <;> rfl
lemma pop_clock (data index value clock acc : BitString) (b : Bool) :
    Function.update (state data index value (b::clock) acc [] [] []) 3 clock=
      state data index value clock acc [] [] [] := by
  funext i;fin_cases i <;> rfl

lemma skipOne_cons (g : BitString → ℕ) (index value clock acc w : BitString) (ws : List BitString) :
    skipOne.Executes g (state (encodeBitList (w::ws)) index value clock acc [] [] [])
      (state (encodeBitList ws) index value clock ((wordChunk w).reverse++acc) [] [] [])
      (11*w.length+18) := by
  convert branchPop_true 0 skip skipBody skipBody g rfl
    (s:=state (encodeBitList (w::ws)) index value clock acc [] [] [])
    (by rw [encodeBitList,pop_data];exact skipBody_executes g index value clock acc w (encodeBitList ws)) using 1 <;> omega

lemma skipOne_nil (g : BitString → ℕ) (index value clock acc : BitString) :
    skipOne.Executes g (state [] index value clock acc [] [] [])
      (state [] index value clock acc [] [] []) 3 :=
  branchPop_empty 0 skip skipBody skipBody g rfl (by simpa using skip_executes g (state [] index value clock acc [] [] []))

/-- The literal clock-controlled loop scans only existing canonical cells and
accumulates their exact encoded acc in reverse order. -/
theorem skipLoop_execution (g : BitString → ℕ) (index value acc : BitString)
    (ws : List BitString) (j : ℕ) :
    ∃t, WhileExecution (3 : Fin 8) skipOne skipOne g
      (state (encodeBitList ws) index value (List.replicate j true) acc [] [] [])
      (state (encodeBitList (ws.drop j)) index value []
        ((encodeBitList (ws.take j)).reverse++acc) [] [] []) t ∧
      t≤j*(11*(encodeBitList ws).length+20)+1 := by
  induction j generalizing ws acc with
  | zero => exact ⟨1,by simpa [encodeBitList] using (WhileExecution.empty
      (state (encodeBitList ws) index value [] acc [] [] []) rfl),by simp⟩
  | succ j ih =>
    cases ws with
    | nil =>
      obtain ⟨t,ht,hb⟩ := ih acc []
      have hc := skipOne_nil g index value (List.replicate j true) acc
      have h := WhileExecution.one
        (show state [] index value (List.replicate (j+1) true) acc [] [] [] 3=true::List.replicate j true from rfl)
        (by simpa only [List.replicate_succ,pop_clock] using hc) ht
      refine ⟨_,by simpa [encodeBitList] using h,?_⟩
      simp [encodeBitList] at hb ⊢;omega
    | cons w ws =>
      obtain ⟨t,ht,hb⟩ := ih ((wordChunk w).reverse++acc) ws
      have hc := skipOne_cons g index value (List.replicate j true) acc w ws
      have h := WhileExecution.one
        (show state (encodeBitList (w::ws)) index value (List.replicate (j+1) true) acc [] [] [] 3=
          true::List.replicate j true from rfl)
        (by simpa only [List.replicate_succ,pop_clock] using hc) ht
      refine ⟨1+(11*w.length+18)+1+t,?_,?_⟩
      · simpa [List.drop_succ_cons,List.take_succ_cons,encodeBitList_eq_chunks,
          List.reverse_append,List.append_assoc] using h
      · have he := CNFCloneEmitter.ClauseLookup.encode_tail_length w ws
        have hw : w.length≤(encodeBitList (w::ws)).length := by simp [encodeBitList];omega
        have hm := Nat.mul_le_mul_left j (show 11*(encodeBitList ws).length+20≤11*(encodeBitList (w::ws)).length+20 by omega)
        nlinarith

lemma parse_queryFree : parse.QueryFree := GraphVerifier.Runtime.unpairOn_queryFree _
lemma emit_queryFree : emit.QueryFree := rename_queryFree _ _ wordEmit_queryFree
lemma skipBody_queryFree : skipBody.QueryFree := seq_queryFree _ _ parse_queryFree
  (seq_queryFree _ _ (clear_queryFree _) emit_queryFree)
lemma skipOne_queryFree : skipOne.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skipBody_queryFree skipBody_queryFree
lemma skipLoop_queryFree : skipLoop.QueryFree := whilePop_queryFree _ _ _ skipOne_queryFree skipOne_queryFree

end HiddenCircuits.DH.Runtime.WordArray
