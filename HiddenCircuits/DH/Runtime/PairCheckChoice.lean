import HiddenCircuits.DH.Runtime.PairCheckModel

/-! Literal pendant-first selection and three distinguishable action tags. -/
namespace HiddenCircuits.DH.Runtime.PairCheck
open Complexity Complexity.OracleBlock

def chooseBits (pendant twin edge : Bool) : BitString :=
  if pendant then [false] else if twin then [true,edge] else []
def choiceStore (pendant twin edge output : BitString) : Store 3 := ![pendant,twin,edge,output]
noncomputable def writeTwin (b : Bool) : OracleBlock 3 := seq (push 3 b) (push 3 true)
noncomputable def chooseTwin : OracleBlock 3 := branchPop 2 (writeTwin false) (writeTwin false) (writeTwin true)
noncomputable def chooseOther : OracleBlock 3 := branchPop 1 (clear 2) (clear 2) chooseTwin
noncomputable def choosePendant : OracleBlock 3 := seq (clear 1) (seq (clear 2) (push 3 false))
noncomputable def choice : OracleBlock 3 := branchPop 0 chooseOther chooseOther choosePendant

lemma writeTwin_executes (g : BitString → ℕ) (b : Bool) :
    (writeTwin b).Executes g (choiceStore [] [] [] []) (choiceStore [] [] [] [true,b]) 4 := by
  have h1 : (push (3 : Fin 4) b).Executes g (choiceStore [] [] [] []) (choiceStore [] [] [] [b]) 1 := by
    convert push_executes g (3 : Fin 4) b (choiceStore [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  have h2 : (push (3 : Fin 4) true).Executes g (choiceStore [] [] [] [b]) (choiceStore [] [] [] [true,b]) 1 := by
    convert push_executes g (3 : Fin 4) true (choiceStore [] [] [] [b]) using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g h1 h2

lemma chooseTwin_executes (g : BitString → ℕ) (b : Bool) :
    chooseTwin.Executes g (choiceStore [] [] [b] []) (choiceStore [] [] [] [true,b]) 6 := by
  have he : Function.update (choiceStore [] [] [b] []) 2 []=choiceStore [] [] [] [] := by
    funext i;fin_cases i <;> rfl
  cases b
  · exact branchPop_false 2 _ _ _ g rfl (by rw [he];exact writeTwin_executes g false)
  · exact branchPop_true 2 _ _ _ g rfl (by rw [he];exact writeTwin_executes g true)

lemma chooseOther_executes (g : BitString → ℕ) (t e : Bool) :
    chooseOther.Executes g (choiceStore [] [t] [e] [])
      (choiceStore [] [] [] (if t then [true,e] else [])) (if t then 8 else 4) := by
  have he : Function.update (choiceStore [] [t] [e] []) 1 []=choiceStore [] [] [e] [] := by
    funext i;fin_cases i <;> rfl
  cases t
  · apply branchPop_false 1 _ _ _ g rfl
    rw [he]
    convert clear_executes g (2 : Fin 4) (choiceStore [] [] [e] []) using 1
    funext i;fin_cases i <;> rfl
  · exact branchPop_true 1 _ _ _ g rfl (by rw [he];exact chooseTwin_executes g e)

lemma choosePendant_executes (g : BitString → ℕ) (t e : Bool) :
    choosePendant.Executes g (choiceStore [] [t] [e] []) (choiceStore [] [] [] [false]) 9 := by
  have h1 : (clear (1 : Fin 4)).Executes g (choiceStore [] [t] [e] []) (choiceStore [] [] [e] []) 2 := by
    convert clear_executes g (1 : Fin 4) (choiceStore [] [t] [e] []) using 1
    funext i;fin_cases i <;> rfl
  have h2 : (clear (2 : Fin 4)).Executes g (choiceStore [] [] [e] []) (choiceStore [] [] [] []) 2 := by
    convert clear_executes g (2 : Fin 4) (choiceStore [] [] [e] []) using 1
    funext i;fin_cases i <;> rfl
  have h3 : (push (3 : Fin 4) false).Executes g (choiceStore [] [] [] []) (choiceStore [] [] [] [false]) 1 := by
    convert push_executes g (3 : Fin 4) false (choiceStore [] [] [] []) using 1
    funext i;fin_cases i <;> rfl
  exact seq_executes _ _ g h1 (seq_executes _ _ g h2 h3)

lemma choice_executes (g : BitString → ℕ) (p t e : Bool) :
    ∃c, choice.Executes g (choiceStore [p] [t] [e] []) (choiceStore [] [] [] (chooseBits p t e)) c ∧ c≤11 := by
  have he : Function.update (choiceStore [p] [t] [e] []) 0 []=choiceStore [] [t] [e] [] := by
    funext i;fin_cases i <;> rfl
  cases p
  · refine ⟨(if t then 8 else 4)+2,?_,by cases t <;> decide⟩
    simpa only [chooseBits,Bool.false_eq_true,↓reduceIte] using
      (branchPop_false 0 chooseOther chooseOther choosePendant g rfl (by rw [he];exact chooseOther_executes g t e))
  · exact ⟨11,branchPop_true 0 chooseOther chooseOther choosePendant g rfl
      (by rw [he];exact choosePendant_executes g t e),by decide⟩

lemma writeTwin_queryFree (b : Bool) : (writeTwin b).QueryFree := seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _)
lemma chooseTwin_queryFree : chooseTwin.QueryFree := branchPop_queryFree _ _ _ _
  (writeTwin_queryFree _) (writeTwin_queryFree _) (writeTwin_queryFree _)
lemma chooseOther_queryFree : chooseOther.QueryFree := branchPop_queryFree _ _ _ _
  (clear_queryFree _) (clear_queryFree _) chooseTwin_queryFree
lemma choosePendant_queryFree : choosePendant.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ (clear_queryFree _) (push_queryFree _ _))
lemma choice_queryFree : choice.QueryFree := branchPop_queryFree _ _ _ _
  chooseOther_queryFree chooseOther_queryFree choosePendant_queryFree

end HiddenCircuits.DH.Runtime.PairCheck
