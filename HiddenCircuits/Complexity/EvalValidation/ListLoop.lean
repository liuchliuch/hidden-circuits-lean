import HiddenCircuits.Complexity.EvalValidation.Core

/-! Every raw stream bit is consumed by actual instructions. Malformed list
markers are recorded as false; every parsed tail is strictly shorter. -/
namespace HiddenCircuits.Complexity.EvalValidation.ListLoop
open OracleBlock GraphVerifier GraphVerifier.Runtime Core
set_option maxHeartbeats 900000
noncomputable def body (pairMode b : Bool) : OracleBlock 31 := seq (push 1 b) (takeAtom pairMode)
noncomputable def program (pairMode : Bool) : OracleBlock 31 := whilePop 1 (body pairMode false) (body pairMode true)

lemma body_executes (g : BitString→ℕ) (pairMode b : Bool) (input xs p width flags : BitString) :
    ∃c,(body pairMode b).Executes g (state input xs p width flags [] [])
      (state input (parse xs).right p width
        (Semantics.atomValid pairMode width (parse xs).left::((parse xs).ok && b)::flags) [] []) c ∧
      c≤1400*(xs.length+p.length+width.length+1) := by
  have hp:(push (1:Fin 32) b).Executes g (state input xs p width flags [] [])
      (state input (b::xs) p width flags [] []) 1 := by
    convert push_executes g (1:Fin 32) b (state input xs p width flags [] []) using 1
    funext i;fin_cases i <;> rfl
  obtain ⟨c,hc,hb⟩:=takeAtom_executes g pairMode input (b::xs) p width flags
  refine ⟨_,seq_executes _ _ g hp hc,?_⟩
  simp only [List.length_cons] at hb
  omega
lemma pop_data (b : Bool) (input xs p width flags : BitString) :
    Function.update (state input (b::xs) p width flags [] []) 1 xs=state input xs p width flags [] [] := by
  funext i;fin_cases i <;> rfl

theorem loop_execution (g : BitString→ℕ) (pairMode : Bool) (input p width xs flags : BitString)
    (N : ℕ) (hx : xs.length≤N) :
    ∃c,WhileExecution (1:Fin 32) (body pairMode false) (body pairMode true) g (state input xs p width flags [] [])
      (state input [] p width (Semantics.runFlags pairMode width xs flags) [] []) c ∧
      c≤xs.length*(1400*(N+p.length+width.length+1)+2)+1 := by
  induction xs using (measure List.length).wf.induction generalizing flags with
  | h xs ih =>
    cases xs with
    | nil =>
      refine ⟨1,?_,by simp⟩
      rw [Semantics.runFlags]
      exact WhileExecution.empty _ rfl
    | cons b xs =>
      obtain ⟨a,ha,hab⟩:=body_executes g pairMode b input xs p width flags
      have ht:(parse xs).right.length≤N:=by have h:=(parse_lengths xs).2;simp only [List.length_cons] at hx;omega
      obtain ⟨c,hc,hcb⟩:=ih (parse xs).right (Field.tail_shorter b xs)
        (Semantics.atomValid pairMode width (parse xs).left::((parse xs).ok && b)::flags) ht
      have hr:(parse xs).right.length+1≤(b::xs).length:=by have h:=(parse_lengths xs).2;simp only [List.length_cons];omega
      have hb':a≤1400*(N+p.length+width.length+1):=hab.trans (by simp only [List.length_cons] at hx;omega)
      refine ⟨1+a+1+c,?_,?_⟩
      · rw [Semantics.runFlags]
        cases b
        · exact WhileExecution.zero rfl (by rw [pop_data];exact ha) hc
        · exact WhileExecution.one rfl (by rw [pop_data];exact ha) hc
      · nlinarith

theorem program_executes (g : BitString→ℕ) (pairMode : Bool) (input p width xs flags : BitString) :
    ∃c,(program pairMode).Executes g (state input xs p width flags [] [])
      (state input [] p width (Semantics.runFlags pairMode width xs flags) [] []) c ∧
      c≤2000*(xs.length+p.length+width.length+1)^2 := by
  obtain ⟨c,hc,hb⟩:=loop_execution g pairMode input p width xs flags xs.length (by rfl)
  refine ⟨c,whilePop_executes _ _ _ g hc,hb.trans ?_⟩
  nlinarith
end HiddenCircuits.Complexity.EvalValidation.ListLoop
