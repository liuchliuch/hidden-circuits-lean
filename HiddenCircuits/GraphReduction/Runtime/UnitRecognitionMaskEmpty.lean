import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionLabelRead
import HiddenCircuits.Complexity.GraphVerifier.RuntimeDecision
import HiddenCircuits.Complexity.BitList

/-! Read-only emptiness testing of the canonical alive mask. Each Boolean word
is physically parsed and folded; a semantic list test is not an instruction. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionMaskEmpty
open Complexity Complexity.OracleBlock

def encoded (ls : List Bool) : BitString := encodeBitList (ls.map (fun b=>[b]))
def state (input stream word out acc : BitString) : Store 5 := fun r=>
  if r.val=0 then input else if r.val=1 then stream else if r.val=2 then word
  else if r.val=4 then out else if r.val=5 then acc else []
def parseEmbedding : Fin 4 ↪ Fin 6 where
  toFun i := ![1,2,3,4] i
  inj' := by decide +kernel

def decisionValue : List Bool → Bool
  | [bit,acc] => acc && !bit
  | _ => false
noncomputable def body : OracleBlock 5 := seq (UnitRecognitionLabelRead.on parseEmbedding)
  (seq (GraphVerifier.Runtime.decision 4 [2,5] decisionValue) (reverseOn 4 5 (by decide)))
noncomputable def loop : OracleBlock 5 := whilePop 1 body body
noncomputable def program : OracleBlock 5 := seq
  (copyOn 0 1 3 (by decide) (by decide) (by decide)) (seq (push 5 true) loop)

lemma encoded_length (ls : List Bool) : (encoded ls).length=4*ls.length := by
  simp [encoded,encodeBitList_length,List.map_map,Function.comp_def]
  omega

lemma body_executes (g : BitString → ℕ) (input : BitString) (b acc : Bool) (rest : List Bool) :
    body.Executes g (state input (pairBits [b] (encoded rest)) [] [] [acc])
      (state input (encoded rest) [] [] [acc && !b]) 27 := by
  have h1 : (UnitRecognitionLabelRead.on parseEmbedding).Executes g
      (state input (pairBits [b] (encoded rest)) [] [] [acc])
      (state input (encoded rest) [b] [] [acc]) 12 := by
    exact UnitRecognitionLabelRead.on_executes parseEmbedding g _ _ [b] (encoded rest)
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim)
  let bits : Fin 6 → Bool := fun r=>if r.val=2 then b else acc
  have h2 : (GraphVerifier.Runtime.decision (4 : Fin 6) [2,5] decisionValue).Executes g
      (state input (encoded rest) [b] [] [acc]) (state input (encoded rest) [] [acc && !b] []) 8 := by
    have h := GraphVerifier.Runtime.decision_executes (4 : Fin 6) [2,5]
      (by decide) (by decide) decisionValue bits g (state input (encoded rest) [b] [] [acc])
      (by intro i hi;fin_cases i <;> simp [state,bits] at *)
    convert h using 1
    funext i;fin_cases i <;> simp [state,bits,eraseStore,decisionValue]
  have h3 : (reverseOn (4 : Fin 6) 5 (by decide)).Executes g
      (state input (encoded rest) [] [acc && !b] []) (state input (encoded rest) [] [] [acc && !b]) 3 := by
    convert reverseOn_executes g (4 : Fin 6) 5 (by decide) _ using 1
    funext i;fin_cases i <;> simp [state]
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)

lemma loop_execution (g : BitString → ℕ) (input : BitString) (ls : List Bool) (acc : Bool) :
    WhileExecution (1 : Fin 6) body body g (state input (encoded ls) [] [] [acc])
      (state input [] [] [] [acc && ls.all Bool.not]) (29*ls.length+1) := by
  induction ls generalizing acc with
  | nil => simpa [encoded,encodeBitList] using (WhileExecution.empty
      (stack := (1 : Fin 6)) (B := body) (C := body) (g := g) (state input [] [] [] [acc]) rfl)
  | cons b bs ih =>
    have h1 := body_executes g input b acc bs
    have ht := ih (acc && !b)
    have he : Function.update (state input (encoded (b::bs)) [] [] [acc]) 1
        (pairBits [b] (encoded bs))=state input (pairBits [b] (encoded bs)) [] [] [acc] := by
      funext i;fin_cases i <;> rfl
    have h := WhileExecution.one
      (show state input (encoded (b::bs)) [] [] [acc] 1=true::pairBits [b] (encoded bs) from rfl)
      (by rw [he];exact h1) ht
    convert h using 1
    · simp [Bool.and_assoc]
    · simp only [List.length_cons];omega

theorem program_executes (g : BitString → ℕ) (ls : List Bool) :
    program.Executes g (state (encoded ls) [] [] [] [])
      (state (encoded ls) [] [] [] [ls.all Bool.not]) (49*ls.length+8) := by
  have h1 : (copyOn (0 : Fin 6) 1 3 (by decide) (by decide) (by decide)).Executes g
      (state (encoded ls) [] [] [] []) (state (encoded ls) (encoded ls) [] [] []) (20*ls.length+2) := by
    convert copyOn_executes g (0 : Fin 6) 1 3 (by decide) (by decide) (by decide)
      (state (encoded ls) [] [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state,encoded_length];ring
  have h2 : (push (5 : Fin 6) true).Executes g
      (state (encoded ls) (encoded ls) [] [] []) (state (encoded ls) (encoded ls) [] [] [true]) 1 := by
    convert push_executes g (5 : Fin 6) true _ using 1
    funext i;fin_cases i <;> rfl
  have h3 := whilePop_executes _ _ _ g (loop_execution g (encoded ls) ls true)
  simp only [Bool.true_and] at h3
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1 <;> omega

lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (UnitRecognitionLabelRead.on_queryFree _)
  (seq_queryFree _ _ (GraphVerifier.Runtime.decision_queryFree _ _ _) (reverseOn_queryFree _ _ _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (push_queryFree _ _) (whilePop_queryFree _ _ _ body_queryFree body_queryFree))

noncomputable def on {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : OracleBlock k := rename program φ

theorem on_executes {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) (g : BitString → ℕ)
    (ls : List Bool) (s : Store k) (hs : s∘φ=state (encoded ls) [] [] [] []) :
    (on φ).Executes g s (Function.update s (φ 5) [ls.all Bool.not]) (49*ls.length+8) := by
  apply rename_executes_to program φ g (program_executes g ls) hs
  · have he : (Function.update s (φ 5) [ls.all Bool.not])∘φ=Function.update (s∘φ) 5 [ls.all Bool.not] := by
      funext i;simp [Function.comp_def,Function.update_apply,φ.injective.eq_iff]
    rw [he,hs]
    funext i;fin_cases i <;> rfl
  · intro i hi;exact Function.update_of_ne (hi 5).symm _ _
lemma on_queryFree {k : ℕ} (φ : Fin 6 ↪ Fin (k+1)) : (on φ).QueryFree := rename_queryFree _ _ program_queryFree

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionMaskEmpty
