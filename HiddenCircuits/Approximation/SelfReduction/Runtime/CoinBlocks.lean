import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery
import Mathlib.Tactic

/-! A physical, bounded coin
splitter consumes a unary clock and reverses the accumulated literal bits. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

def coinStore (coins clock chunk tmp : BitString) : Store 3 :=
  fun i => if i.val=0 then coins else if i.val=1 then clock else if i.val=2 then chunk else tmp

noncomputable def takeCoinsLoop : OracleBlock 3 :=
  whilePop 1 (branchPop 0 (push 3 false) (push 3 false) (push 3 true))
    (branchPop 0 (push 3 false) (push 3 false) (push 3 true))

noncomputable def takeCoins : OracleBlock 3 :=
  seq takeCoinsLoop (reverseOn 3 2 (by decide))

theorem takeCoinsLoop_execution (g : BitString → ℕ) (xs rest acc : BitString) :
    WhileExecution (1 : Fin 4)
      (branchPop 0 (push 3 false) (push 3 false) (push 3 true))
      (branchPop 0 (push 3 false) (push 3 false) (push 3 true)) g
      (coinStore (xs++rest) (List.replicate xs.length true) [] acc)
      (coinStore rest [] [] (xs.reverse++acc)) (5*xs.length+1) := by
  induction xs generalizing acc with
  | nil => simpa using (WhileExecution.empty (coinStore rest [] [] acc) (by rfl))
  | cons b xs ih =>
    have hpop : Function.update (coinStore ((b::xs)++rest) (List.replicate (b::xs).length true) [] acc)
        (1 : Fin 4) (List.replicate xs.length true) =
        coinStore (b::(xs++rest)) (List.replicate xs.length true) [] acc := by
      funext i; fin_cases i <;> rfl
    have hbody : (branchPop (0 : Fin 4) (push 3 false) (push 3 false) (push 3 true)).Executes g
        (coinStore (b::(xs++rest)) (List.replicate xs.length true) [] acc)
        (coinStore (xs++rest) (List.replicate xs.length true) [] (b::acc)) 3 := by
      cases b with
      | false =>
        apply branchPop_false _ _ _ _ g rfl
        convert push_executes g (3 : Fin 4) false (coinStore (xs++rest) (List.replicate xs.length true) [] acc) using 1
        all_goals funext i; fin_cases i <;> rfl
      | true =>
        apply branchPop_true _ _ _ _ g rfl
        convert push_executes g (3 : Fin 4) true (coinStore (xs++rest) (List.replicate xs.length true) [] acc) using 1
        all_goals funext i; fin_cases i <;> rfl
    have hh := WhileExecution.one
      (s := coinStore ((b::xs)++rest) (List.replicate (b::xs).length true) [] acc)
      (rest := List.replicate xs.length true) (by rfl) (by rw [hpop]; exact hbody) (ih (b::acc))
    convert hh using 1
    · simp [List.reverse_cons,List.append_assoc]
    · simp only [List.length_cons]; omega

 theorem takeCoins_executes (g : BitString → ℕ) (xs rest : BitString) :
    takeCoins.Executes g (coinStore (xs++rest) (List.replicate xs.length true) [] [])
      (coinStore rest [] xs []) (7*xs.length+4) := by
  have hl := whilePop_executes _ _ _ _ (takeCoinsLoop_execution g xs rest [])
  have hr : (reverseOn (3 : Fin 4) 2 (by decide)).Executes g
      (coinStore rest [] [] xs.reverse) (coinStore rest [] xs []) (2*xs.length+1) := by
    convert reverseOn_executes g (3 : Fin 4) 2 (by decide)
      (coinStore rest [] [] xs.reverse) using 1
    · funext i; fin_cases i <;> simp [coinStore]
    · simp [coinStore]
  have h := seq_executes _ _ g (by simpa using hl) hr
  convert h using 1 <;> omega

 theorem takeCoins_queryFree : takeCoins.QueryFree :=
  seq_queryFree _ _ (whilePop_queryFree _ _ _
    (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))
    (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _)))
    (reverseOn_queryFree _ _ _)

end HiddenCircuits.Approximation.SelfReduction.Runtime
