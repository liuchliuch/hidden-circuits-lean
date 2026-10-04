import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit
import HiddenCircuits.Complexity.OracleCleanup

/-! The fixed six-stack machine emits the unary rows of the identity permutation. -/
namespace HiddenCircuits.Approximation.SamplerRuntime.Identity
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

/-- Consecutive unary addresses, in increasing order. -/
def words (start : ℕ) : ℕ → List BitString
  | 0 => []
  | n+1 => List.replicate start true :: words (start+1) n

def evaluate (clock : BitString) : BitString := encodeBitList (words 0 clock.length)

theorem words_encode_length (start n : ℕ) :
    (encodeBitList (words start n)).length=n*(2*start+n+1) := by
  induction n generalizing start with
  | zero => simp [words,encodeBitList]
  | succ n ih =>
    simp only [words,encodeBitList,List.length_cons,pairBits_length,List.length_replicate,ih]
    ring

theorem words_ofFn (start n : ℕ) :
    words start n=List.ofFn (fun i : Fin n => List.replicate (start+i.val) true) := by
  induction n generalizing start with
  | zero => simp [words]
  | succ n ih =>
    rw [words,List.ofFn_succ,ih]
    congr 1
    apply congrArg List.ofFn
    funext i
    congr 1
    simp only [Fin.val_succ]
    omega

theorem evaluate_unary (n : ℕ) : evaluate (List.replicate n true)=
    encodeBitList (List.ofFn (fun i : Fin n => List.replicate i.val true)) := by
  simp only [evaluate,List.length_replicate,words_ofFn,Nat.zero_add]

def state (input acc clock : BitString) (index : ℕ) (temporary word : BitString) : Store 5 := fun r =>
  if r.val=0 then input else if r.val=1 then acc else if r.val=2 then clock
  else if r.val=3 then List.replicate index true else if r.val=4 then temporary else word

def emitMap : Fin 2 ↪ Fin 6 where
  toFun i := if i.val=0 then 5 else 1
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def emit : OracleBlock 5 := rename wordEmit emitMap
noncomputable def body : OracleBlock 5 := seq (copyOn 3 5 4 (by decide) (by decide) (by decide))
  (seq emit (push 3 true))
noncomputable def loop : OracleBlock 5 := whilePop 2 body body
noncomputable def finish : OracleBlock 5 := seq (clear 0) (seq (clear 3) (reverseOn 1 0 (by decide)))
noncomputable def program : OracleBlock 5 := seq (copyOn 0 2 4 (by decide) (by decide) (by decide))
  (seq loop finish)

lemma body_executes (g : BitString → ℕ) (input acc clock : BitString) (i : ℕ) :
    body.Executes g (state input acc clock i [] [])
      (state input ((wordChunk (List.replicate i true)).reverse++acc) clock (i+1) [] []) (11*i+14) := by
  have hc : (copyOn (3:Fin 6) 5 4 (by decide) (by decide) (by decide)).Executes g
      (state input acc clock i [] []) (state input acc clock i [] (List.replicate i true)) (5*i+2) := by
    convert copyOn_executes g (3:Fin 6) 5 4 (by decide) (by decide) (by decide)
      (state input acc clock i [] []) rfl using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have he : emit.Executes g (state input acc clock i [] (List.replicate i true))
      (state input ((wordChunk (List.replicate i true)).reverse++acc) clock i [] []) (6*i+7) := by
    convert rename_executes_to wordEmit emitMap g (wordEmit_executes g (List.replicate i true) acc)
      (outerS:=state input acc clock i [] (List.replicate i true))
      (outerT:=state input ((wordChunk (List.replicate i true)).reverse++acc) clock i [] [])
      (by funext r;fin_cases r <;> rfl) (by funext r;fin_cases r <;> rfl)
      (by intro r hr;fin_cases r <;> first | rfl | exact False.elim (hr 0 rfl) | exact False.elim (hr 1 rfl)) using 1
    simp
  have hp : (push (3:Fin 6) true).Executes g
      (state input ((wordChunk (List.replicate i true)).reverse++acc) clock i [] [])
      (state input ((wordChunk (List.replicate i true)).reverse++acc) clock (i+1) [] []) 1 := by
    convert push_executes g (3:Fin 6) true _ using 1
    funext r;fin_cases r <;> simp [state,List.replicate_succ]
  convert seq_executes _ _ g hc (seq_executes _ _ g he hp) using 1 <;> omega

lemma pop_clock (input acc clock : BitString) (i : ℕ) (b : Bool) :
    Function.update (state input acc (b::clock) i [] []) 2 clock=state input acc clock i [] [] := by
  funext r;fin_cases r <;> rfl

lemma loop_execution (g : BitString → ℕ) (input clock acc : BitString) (i : ℕ) :
    ∃t,WhileExecution (2:Fin 6) body body g (state input acc clock i [] [])
      (state input ((encodeBitList (words i clock.length)).reverse++acc) [] (i+clock.length) [] []) t ∧
      t≤16*clock.length*(i+clock.length+1)+1 := by
  induction clock generalizing i acc with
  | nil => exact ⟨1,by simpa [words,encodeBitList] using (WhileExecution.empty
      (stack:=(2:Fin 6)) (B:=body) (C:=body) (g:=g) (state input acc [] i [] []) rfl),by simp⟩
  | cons b clock ih =>
    obtain ⟨t,ht,hb⟩ := ih ((wordChunk (List.replicate i true)).reverse++acc) (i+1)
    have hbody := body_executes g input acc clock i
    rw [←pop_clock input acc clock i b] at hbody
    have h : WhileExecution (2:Fin 6) body body g (state input acc (b::clock) i [] [])
        (state input ((encodeBitList (words (i+1) clock.length)).reverse++
          ((wordChunk (List.replicate i true)).reverse++acc)) [] (i+1+clock.length) [] [])
        (1+(11*i+14)+1+t) := by
      cases b
      · exact WhileExecution.zero rfl hbody ht
      · exact WhileExecution.one rfl hbody ht
    refine ⟨1+(11*i+14)+1+t,?_,?_⟩
    · convert h using 1 <;> simp [words,encodeBitList_eq_chunks,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp only [List.length_cons]
      nlinarith

lemma finish_executes (g : BitString → ℕ) (input acc : BitString) (i : ℕ) :
    finish.Executes g (state input acc [] i [] []) (state acc.reverse [] [] 0 [] [])
      (input.length+i+2*acc.length+7) := by
  have h0 : (clear (0:Fin 6)).Executes g (state input acc [] i [] [])
      (state [] acc [] i [] []) (input.length+1) := by
    convert clear_executes g (0:Fin 6) _ using 1
    funext r;fin_cases r <;> rfl
  have h3 : (clear (3:Fin 6)).Executes g (state [] acc [] i [] [])
      (state [] acc [] 0 [] []) (i+1) := by
    convert clear_executes g (3:Fin 6) _ using 1
    · funext r;fin_cases r <;> simp [state]
    · simp [state]
  have h1 : (reverseOn (1:Fin 6) 0 (by decide)).Executes g (state [] acc [] 0 [] [])
      (state acc.reverse [] [] 0 [] []) (2*acc.length+1) := by
    convert reverseOn_executes g (1:Fin 6) 0 (by decide) _ using 1
    funext r;fin_cases r <;> simp [state]
  convert seq_executes _ _ g h0 (seq_executes _ _ g h3 h1) using 1 <;> omega

/-- Every raw clock is physically scanned; its bit values may be arbitrary. -/
theorem program_executes (g : BitString → ℕ) (clock : BitString) :
    ∃t,program.Executes g (state clock [] [] 0 [] []) (state (evaluate clock) [] [] 0 [] []) t ∧
      t≤40*(clock.length+1)^2 := by
  have hc : (copyOn (0:Fin 6) 2 4 (by decide) (by decide) (by decide)).Executes g
      (state clock [] [] 0 [] []) (state clock [] clock 0 [] []) (5*clock.length+2) := by
    convert copyOn_executes g (0:Fin 6) 2 4 (by decide) (by decide) (by decide) (state clock [] [] 0 [] []) rfl using 1
    funext r;fin_cases r <;> simp [state]
  obtain ⟨t,ht,hb⟩ := loop_execution g clock clock [] 0
  simp only [List.append_nil,Nat.zero_add] at ht hb
  have hf := finish_executes g clock (encodeBitList (words 0 clock.length)).reverse clock.length
  rw [List.reverse_reverse] at hf
  refine ⟨_,seq_executes _ _ g hc (seq_executes _ _ g (whilePop_executes _ _ _ g ht) hf),?_⟩
  simp only [List.length_reverse,words_encode_length,Nat.mul_zero,Nat.zero_add]
  nlinarith

lemma emit_queryFree : emit.QueryFree := rename_queryFree _ _ wordEmit_queryFree
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ emit_queryFree (push_queryFree _ _))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (whilePop_queryFree _ _ _ body_queryFree body_queryFree)
    (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (reverseOn_queryFree _ _ _))))

theorem evaluate_polyTime : PolyTime evaluate := by
  apply polyTime_of_block program program_queryFree (40*(Polynomial.X+1)^2)
  intro clock
  obtain ⟨t,ht,hb⟩ := program_executes (fun _ => 0) clock
  refine ⟨state (evaluate clock) [] [] 0 [] [],t,?_,rfl,?_⟩
  · convert ht using 1
    funext r;fin_cases r <;> rfl
  · simpa using hb

end HiddenCircuits.Approximation.SamplerRuntime.Identity
