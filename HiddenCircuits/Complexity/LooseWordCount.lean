import HiddenCircuits.Complexity.LooseWordList

/-! Total unary field counting with physical parsing and cleanup on arbitrary bytes. -/
namespace HiddenCircuits.Complexity.LooseWordCount
open OracleBlock GraphVerifier GraphVerifier.Runtime

def state (input stream word flag : BitString) (count : ℕ) : Store 5 := fun i=>
  if i.val=0 then input else if i.val=1 then stream else if i.val=2 then word
  else if i.val=4 then flag else if i.val=5 then List.replicate count true else []
def parseMap : Fin 4 ↪ Fin 6 where
  toFun i := ![1,2,3,4] i
  inj' := by decide +kernel
noncomputable def body : OracleBlock 5 := seq (unpairOn parseMap)
  (seq (clear 2) (seq (clear 4) (push 5 true)))
noncomputable def loop : OracleBlock 5 := whilePop 1 body body
noncomputable def program : OracleBlock 5 := seq (copyOn 0 1 3 (by decide) (by decide) (by decide)) loop

theorem body_executes (g : BitString → ℕ) (input xs : BitString) (n : ℕ) :
    ∃c,body.Executes g (state input xs [] [] n) (state input (parse xs).right [] [] (n+1)) c ∧c≤6*xs.length+20 := by
  have hp : (unpairOn parseMap).Executes g (state input xs [] [] n)
      (state input (parse xs).right (parse xs).left [(parse xs).ok] n)
      (parseCost xs+2*(parse xs).left.length+1) := by
    apply unpairOn_executes
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim | exact (hi 2 rfl).elim | exact (hi 3 rfl).elim
  have hc : (clear (2:Fin 6)).Executes g (state input (parse xs).right (parse xs).left [(parse xs).ok] n)
      (state input (parse xs).right [] [(parse xs).ok] n) ((parse xs).left.length+1) := by
    convert clear_executes g (2:Fin 6) (state input (parse xs).right (parse xs).left [(parse xs).ok] n) using 1
    funext i;fin_cases i <;> rfl
  have hf : (clear (4:Fin 6)).Executes g (state input (parse xs).right [] [(parse xs).ok] n)
      (state input (parse xs).right [] [] n) 2 := by
    convert clear_executes g (4:Fin 6) (state input (parse xs).right [] [(parse xs).ok] n) using 1
    funext i;fin_cases i <;> rfl
  have hi : (push (5:Fin 6) true).Executes g (state input (parse xs).right [] [] n)
      (state input (parse xs).right [] [] (n+1)) 1 := by
    convert push_executes g (5:Fin 6) true (state input (parse xs).right [] [] n) using 1
    funext i;fin_cases i <;> simp [state,List.replicate_succ]
  refine ⟨_,seq_executes _ _ g hp (seq_executes _ _ g hc (seq_executes _ _ g hf hi)),?_⟩
  have ht:=unpair_cost_bound xs
  have hl:=(parse_lengths xs).1
  omega

theorem loop_executes (g : BitString → ℕ) (input xs : BitString) (n : ℕ) :
    ∃c,WhileExecution (1:Fin 6) body body g (state input xs [] [] n)
      (state input [] [] [] (n+(LooseWordList.words xs).length)) c ∧c≤30*(xs.length+1)^2 := by
  induction xs using (measure List.length).wf.induction generalizing n with
  | h xs ih =>
    cases xs with
    | nil => exact ⟨1,by simpa using WhileExecution.empty (state input [] [] [] n) rfl,by simp⟩
    | cons b bs =>
      have hl:=(parse_lengths bs).2
      obtain ⟨a,ha,hba⟩:=body_executes g input bs n
      obtain ⟨c,hc,hbc⟩:=ih (parse bs).right (by change (parse bs).right.length<(b::bs).length;simp;omega) (n+1)
      have hu : Function.update (state input (b::bs) [] [] n) 1 bs=state input bs [] [] n := by funext i;fin_cases i <;> rfl
      have hh : WhileExecution (1:Fin 6) body body g (state input (b::bs) [] [] n)
          (state input [] [] [] (n+1+(LooseWordList.words (parse bs).right).length)) (1+a+1+c) := by
        cases b
        · exact WhileExecution.zero rfl (by rw [hu];exact ha) hc
        · exact WhileExecution.one rfl (by rw [hu];exact ha) hc
      refine ⟨1+a+1+c,?_,?_⟩
      · simpa only [LooseWordList.words_cons,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
      · have hs:((parse bs).right.length+1)^2≤(bs.length+1)^2 := by gcongr
        simp only [List.length_cons]
        nlinarith

theorem program_executes (g : BitString → ℕ) (xs : BitString) :
    ∃c,program.Executes g (state xs [] [] [] 0) (state xs [] [] [] (LooseWordList.words xs).length) c ∧
      c≤40*(xs.length+1)^2 := by
  have hc : (copyOn (0:Fin 6) 1 3 (by decide) (by decide) (by decide)).Executes g (state xs [] [] [] 0)
      (state xs xs [] [] 0) (5*xs.length+2) := by
    convert copyOn_executes g (0:Fin 6) 1 3 (by decide) (by decide) (by decide) (state xs [] [] [] 0) rfl using 1
    funext i;fin_cases i <;> simp [state]
  obtain ⟨c,ht,hb⟩:=loop_executes g xs xs 0
  simp only [Nat.zero_add] at ht
  exact ⟨_,seq_executes _ _ g hc (whilePop_executes _ _ _ g ht),by nlinarith⟩
lemma body_queryFree : body.QueryFree := seq_queryFree _ _ (unpairOn_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _)))
lemma program_queryFree : program.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (whilePop_queryFree _ _ _ body_queryFree body_queryFree)
end HiddenCircuits.Complexity.LooseWordCount
