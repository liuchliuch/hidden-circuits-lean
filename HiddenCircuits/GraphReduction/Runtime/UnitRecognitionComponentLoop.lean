import HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponentBody

/-! A literal original-n component clock. A stopped component simply stutters
through the remaining bounded iterations; the label/mask data is unchanged. -/
namespace HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
open Complexity Complexity.OracleBlock DH.Runtime.PairCheck

noncomputable def loop : OracleBlock 36 := whilePop 34 body body
noncomputable def runProgram : OracleBlock 36 := seq
  (copyOn 0 34 15 (by decide) (by decide) (by decide)) loop

lemma pop_clock {n : ℕ} (G : MatrixData n) (A : Vector Bool n) (s : Data n)
    (clock : BitString) (b : Bool) :
    Function.update (store G A s (b::clock) [] [] [] [false] [] []) (34 : Fin 37) clock=
      store G A s clock [] [] [] [false] [] [] := by
  funext i;fin_cases i <;> rfl

lemma loop_execution (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (m : ℕ) (s : Data n) :
    ∃t, WhileExecution (34 : Fin 37) body body g
      (store G A s (List.replicate m true) [] [] [] [false] [] [])
      (store G A (run G A m s) [] [] [] [] [false] [] []) t ∧ t≤m*(2000*(n+1)^4+2)+1 := by
  induction m generalizing s with
  | zero =>
    exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
  | succ m ih =>
    obtain ⟨c,hc,hcb⟩ := body_executes g G A s (List.replicate m true)
    obtain ⟨t,ht,htb⟩ := ih (step G A s)
    refine ⟨1+c+1+t,?_,?_⟩
    · exact WhileExecution.one
        (show store G A s (List.replicate (m+1) true) [] [] [] [false] [] [] 34 =
          true::List.replicate m true from rfl)
        (by simpa only [List.replicate_succ,pop_clock] using hc) ht
    · nlinarith

theorem runProgram_executes (g : BitString → ℕ) {n : ℕ} (G : MatrixData n)
    (A : Vector Bool n) (s : Data n) :
    ∃t, runProgram.Executes g (store G A s [] [] [] [] [false] [] [])
      (store G A (run G A n s) [] [] [] [] [false] [] []) t ∧ t≤2100*(n+1)^5 := by
  have hc : (copyOn (0 : Fin 37) 34 15 (by decide) (by decide) (by decide)).Executes g
      (store G A s [] [] [] [] [false] [] [])
      (store G A s (List.replicate n true) [] [] [] [false] [] []) (5*n+2) := by
    convert copyOn_executes g (0 : Fin 37) 34 15 (by decide) (by decide) (by decide)
      (store G A s [] [] [] [] [false] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store,UnitRecognitionChoice.rawState]
    · simp [store,UnitRecognitionChoice.rawState]
  obtain ⟨c,h,hb⟩ := loop_execution g G A n s
  refine ⟨_,seq_executes _ _ g hc (whilePop_executes _ _ _ g h),?_⟩
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5)]

lemma runProgram_queryFree : runProgram.QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (whilePop_queryFree _ _ _ body_queryFree body_queryFree)

end HiddenCircuits.GraphReduction.Runtime.UnitRecognitionComponent
