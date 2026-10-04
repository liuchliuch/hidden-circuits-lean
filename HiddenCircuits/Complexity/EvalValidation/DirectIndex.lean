import HiddenCircuits.Complexity.EvalValidation.IndexDefs

/-! A direct raw unary-index validator. Two width positions are reserved, then
one width bit is physically consumed for each index bit. No arithmetic or
comparison machine is treated as a runtime primitive. -/
namespace HiddenCircuits.Complexity.EvalValidation.DirectIndex
open OracleBlock GraphVerifier.Runtime
set_option maxHeartbeats 800000

def state (xs width counter : BitString) (flag : Bool) : Store 8 := Index.store xs width [flag] counter [] [] []
noncomputable def takeWidth : OracleBlock 8 := branchPop 3 (writeBool 2 false) skip skip
noncomputable def flagBit (b : Bool) : OracleBlock 8 := if b then skip else writeBool 2 false
noncomputable def body (b : Bool) : OracleBlock 8 := seq (flagBit b) takeWidth
noncomputable def loop : OracleBlock 8 := whilePop 0 (body false) (body true)
noncomputable def setup : OracleBlock 8 := seq (copyOn 1 3 4 (by decide) (by decide) (by decide)) (push 2 true)
noncomputable def reserve : OracleBlock 8 := seq takeWidth takeWidth
noncomputable def program : OracleBlock 8 := seq setup (seq reserve (seq loop (clear 3)))

lemma takeWidth_executes (g : BitString→ℕ) (xs width counter : BitString) (flag : Bool) :
    ∃c,takeWidth.Executes g (state xs width counter flag) (state xs width counter.tail (flag && !counter.isEmpty)) c ∧ c≤7 := by
  cases counter with
  | nil =>
    have hw:(writeBool (2:Fin 9) false).Executes g (state xs width [] flag) (state xs width [] false) 5 := by
      convert writeBool_executes (2:Fin 9) false g (state xs width [] flag) using 1
      funext i;fin_cases i <;> rfl
    exact ⟨7,by simpa using branchPop_empty (3:Fin 9) (writeBool 2 false) skip skip g rfl hw,by decide⟩
  | cons b counter =>
    have he:Function.update (state xs width (b::counter) flag) (3:Fin 9) counter=state xs width counter flag := by
      funext i;fin_cases i <;> rfl
    cases b
    · refine ⟨3,?_,by decide⟩
      simpa using branchPop_false (3:Fin 9) (writeBool 2 false) skip skip g
        (s:=state xs width (false::counter) flag) rfl (by rw [he];exact skip_executes g (state xs width counter flag))
    · refine ⟨3,?_,by decide⟩
      simpa using branchPop_true (3:Fin 9) (writeBool 2 false) skip skip g
        (s:=state xs width (true::counter) flag) rfl (by rw [he];exact skip_executes g (state xs width counter flag))
lemma flagBit_executes (g : BitString→ℕ) (b : Bool) (xs width counter : BitString) (flag : Bool) :
    ∃c,(flagBit b).Executes g (state xs width counter flag) (state xs width counter (flag && b)) c ∧ c≤5 := by
  cases b
  · refine ⟨5,?_,by decide⟩
    convert writeBool_executes (2:Fin 9) false g (state xs width counter flag) using 1
    funext i;fin_cases i <;> simp [state,Index.store]
  · exact ⟨1,by simpa only [Bool.and_true] using skip_executes g (state xs width counter flag),by decide⟩
lemma body_executes (g : BitString→ℕ) (b : Bool) (xs width counter : BitString) (flag : Bool) :
    ∃c,(body b).Executes g (state xs width counter flag)
      (state xs width counter.tail ((flag && b) && !counter.isEmpty)) c ∧ c≤14 := by
  obtain ⟨a,ha,hab⟩:=flagBit_executes g b xs width counter flag
  obtain ⟨c,hc,hcb⟩:=takeWidth_executes g xs width counter (flag && b)
  exact ⟨_,seq_executes _ _ g ha hc,by omega⟩
lemma pop_xs (b : Bool) (xs width counter : BitString) (flag : Bool) :
    Function.update (state (b::xs) width counter flag) (0:Fin 9) xs=state xs width counter flag := by
  funext i;fin_cases i <;> rfl
lemma next_flag (b flag : Bool) (xs counter : BitString) :
    (((flag && b) && !counter.isEmpty) && xs.all id && decide (xs.length≤counter.tail.length))=
      (flag && (b::xs).all id && decide ((b::xs).length≤counter.length)) := by
  cases counter <;> simp [Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]

theorem loop_execution (g : BitString→ℕ) (xs width counter : BitString) (flag : Bool) :
    ∃c,WhileExecution (0:Fin 9) (body false) (body true) g (state xs width counter flag)
      (state [] width (counter.drop xs.length) (flag && xs.all id && decide (xs.length≤counter.length))) c ∧ c≤16*xs.length+1 := by
  induction xs generalizing counter flag with
  | nil => exact ⟨1,by simpa using WhileExecution.empty (stack:=(0:Fin 9)) (B:=body false) (C:=body true) (g:=g) (state [] width counter flag) rfl,by simp⟩
  | cons b xs ih =>
    obtain ⟨a,ha,hab⟩:=body_executes g b xs width counter flag
    obtain ⟨c,hc,hcb⟩:=ih counter.tail ((flag && b) && !counter.isEmpty)
    rw [next_flag] at hc
    have hd:counter.tail.drop xs.length=counter.drop (b::xs).length:=by cases counter <;> simp
    rw [hd] at hc
    refine ⟨1+a+1+c,?_,?_⟩
    · cases b
      · exact WhileExecution.zero rfl (by rw [pop_xs];exact ha) hc
      · exact WhileExecution.one rfl (by rw [pop_xs];exact ha) hc
    · simp only [List.length_cons];omega
lemma setup_executes (g : BitString→ℕ) (xs width : BitString) :
    setup.Executes g (Index.store xs width [] [] [] [] []) (state xs width width true) (5*width.length+5) := by
  have h1:(copyOn (1:Fin 9) 3 4 (by decide) (by decide) (by decide)).Executes g
      (Index.store xs width [] [] [] [] []) (Index.store xs width [] width [] [] []) (5*width.length+2) := by
    convert copyOn_executes g (1:Fin 9) 3 4 (by decide) (by decide) (by decide) (Index.store xs width [] [] [] [] []) rfl using 1
    funext i;fin_cases i <;> simp [Index.store]
  have h2:(push (2:Fin 9) true).Executes g (Index.store xs width [] width [] [] []) (state xs width width true) 1 := by
    convert push_executes g (2:Fin 9) true (Index.store xs width [] width [] [] []) using 1
    funext i;fin_cases i <;> rfl
  convert seq_executes _ _ g h1 h2 using 1 <;> omega
lemma reserved_valid (xs width : BitString) :
    (((true && !width.isEmpty) && !width.tail.isEmpty) && xs.all id && decide (xs.length≤width.tail.tail.length))=Index.valid xs width := by
  cases width with
  | nil => simp [Index.valid]
  | cons a width =>
    cases width with
    | nil => simp [Index.valid]
    | cons b width => simp [Index.valid,Nat.add_assoc]

theorem program_executes (g : BitString→ℕ) (xs width : BitString) :
    ∃c,program.Executes g (Index.store xs width [] [] [] [] [])
      (Index.store [] width [Index.valid xs width] [] [] [] []) c ∧ c≤100*(xs.length+width.length+1) := by
  have hi:=setup_executes g xs width
  obtain ⟨a,ha,hab⟩:=takeWidth_executes g xs width width true
  obtain ⟨b,hb,hbb⟩:=takeWidth_executes g xs width width.tail (true && !width.isEmpty)
  obtain ⟨c,hc,hcb⟩:=loop_execution g xs width width.tail.tail ((true && !width.isEmpty) && !width.tail.isEmpty)
  rw [reserved_valid] at hc
  have hl:=whilePop_executes _ _ _ g hc
  have hz:(clear (3:Fin 9)).Executes g (state [] width (width.tail.tail.drop xs.length) (Index.valid xs width))
      (Index.store [] width [Index.valid xs width] [] [] [] []) ((width.tail.tail.drop xs.length).length+1) := by
    convert clear_executes g (3:Fin 9) (state [] width (width.tail.tail.drop xs.length) (Index.valid xs width)) using 1
    funext i;fin_cases i <;> rfl
  refine ⟨_,seq_executes _ _ g hi (seq_executes _ _ g (seq_executes _ _ g ha hb) (seq_executes _ _ g hl hz)),?_⟩
  have hlen:(width.tail.tail.drop xs.length).length≤width.length := by simp only [List.length_drop,List.length_tail];omega
  clear hc hl hi ha hb hz
  omega
end HiddenCircuits.Complexity.EvalValidation.DirectIndex
