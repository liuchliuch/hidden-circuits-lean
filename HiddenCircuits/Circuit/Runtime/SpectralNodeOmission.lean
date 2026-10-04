import HiddenCircuits.DH.Runtime.WordArray
import HiddenCircuits.Complexity.OracleMove
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorRuntime

/-! Indexed deletion preserves the literal order of every other spectral node. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralNodeOmission
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic HiddenCircuits.DH.Runtime.WordArray

noncomputable def extractBody : OracleBlock 7 := seq parse (seq (clear 7)
  (moveOn 5 2 6 (by decide) (by decide) (by decide)))
noncomputable def extractOne : OracleBlock 7 := branchPop 0 skip extractBody extractBody
noncomputable def program : OracleBlock 7 :=
  seq (copyOn 1 3 6 (by decide) (by decide) (by decide))
    (seq skipLoop (seq extractOne finish))

theorem extractBody_executes (oracle : BitString → ℕ) (index acc word rest : BitString) :
    extractBody.Executes oracle (state (pairBits word rest) index [] [] acc [] [] [])
      (state rest index word [] acc [] [] []) (11*word.length+14) := by
  have hp := parse_executes oracle index [] [] acc word rest
  have hc : (clear (7:Fin 8)).Executes oracle (state rest index [] [] acc word [] [true])
      (state rest index [] [] acc word [] []) 2 := by
    convert clear_executes oracle (7:Fin 8) (state rest index [] [] acc word [] [true]) using 1
    funext i;fin_cases i <;> simp [state]
  have hm : (moveOn (5:Fin 8) 2 6 (by decide) (by decide) (by decide)).Executes oracle
      (state rest index [] [] acc word [] []) (state rest index word [] acc [] [] []) (6*word.length+5) := by
    convert moveOn_executes oracle (5:Fin 8) 2 6 (by decide) (by decide) (by decide)
      (state rest index [] [] acc word [] []) rfl using 1
    funext i;fin_cases i <;> simp [state]
  convert seq_executes _ _ oracle hp (seq_executes _ _ oracle hc hm) using 1 <;> omega

theorem extractOne_cons (oracle : BitString → ℕ) (index acc word : BitString) (ws : List BitString) :
    extractOne.Executes oracle (state (encodeBitList (word::ws)) index [] [] acc [] [] [])
      (state (encodeBitList ws) index word [] acc [] [] []) (11*word.length+16) := by
  convert branchPop_true 0 skip extractBody extractBody oracle rfl
    (s:=state (encodeBitList (word::ws)) index [] [] acc [] [] [])
    (by rw [encodeBitList,pop_data];exact extractBody_executes oracle index acc word (encodeBitList ws)) using 1 <;> omega

theorem program_executes (oracle : BitString → ℕ) (ws : List BitString) (j : ℕ) (hj : j<ws.length) :
    ∃t, program.Executes oracle (store (encodeBitList ws) (List.replicate j true) [])
      (store (encodeBitList (ws.eraseIdx j)) (List.replicate j true) ws[j]) t ∧
      t≤100*((encodeBitList ws).length+j+1)^2 := by
  have hc : (copyOn (1:Fin 8) 3 6 (by decide) (by decide) (by decide)).Executes oracle
      (store (encodeBitList ws) (List.replicate j true) [])
      (state (encodeBitList ws) (List.replicate j true) [] (List.replicate j true) [] [] [] []) (5*j+2) := by
    convert copyOn_executes oracle (1:Fin 8) 3 6 (by decide) (by decide) (by decide)
      (store (encodeBitList ws) (List.replicate j true) []) rfl using 1
    · funext i;fin_cases i <;> simp [state,store]
    · simp [state,store]
  obtain ⟨a,ha,hab⟩ := skipLoop_execution oracle (List.replicate j true) [] [] ws j
  simp only [List.append_nil] at ha
  have he := extractOne_cons oracle (List.replicate j true) (encodeBitList (ws.take j)).reverse ws[j] (ws.drop (j+1))
  rw [←List.drop_eq_getElem_cons hj] at he
  have hf := finish_executes oracle (encodeBitList (ws.drop (j+1))) (List.replicate j true) ws[j]
    (encodeBitList (ws.take j)).reverse
  have hh := seq_executes _ _ oracle hc (seq_executes _ _ oracle (whilePop_executes _ _ _ oracle ha)
    (seq_executes _ _ oracle he hf))
  refine ⟨5*j+2+(a+(11*ws[j].length+16+(4*(encodeBitList (ws.drop (j+1))).length+2*((encodeBitList (ws.take j)).reverse).length+4)+2)+2)+2,?_,?_⟩
  · simpa only [List.reverse_reverse,←encodeBitList_append,←List.eraseIdx_eq_take_drop_succ] using hh
  · have hd := CNFCloneEmitter.ClauseLookup.encode_drop_length ws (j+1)
    have ht := encode_take_length ws j
    have hw := member_length_le_encodeBitList (List.getElem_mem hj : ws[j]∈ws)
    simp only [List.length_reverse]
    nlinarith

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
    (seq_queryFree _ _ skipLoop_queryFree
      (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree
        (seq_queryFree _ _ parse_queryFree (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _)))
        (seq_queryFree _ _ parse_queryFree (seq_queryFree _ _ (clear_queryFree _) (moveOn_queryFree _ _ _ _ _ _)))) finish_queryFree))
end HiddenCircuits.Circuit.Runtime.SpectralNodeOmission
