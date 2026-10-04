import HiddenCircuits.Approximation.SelfReduction.Runtime.CoinBlocks
import HiddenCircuits.Approximation.SelfReduction.MatchingDeletion

/-! Concrete bit-mask deletion of an indexed retained vertex. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

noncomputable def replaceFalse : OracleBlock 3 := branchPop 0 skip (push 0 false) (push 0 false)
noncomputable def clearAt : OracleBlock 3 := seq takeCoinsLoop (seq replaceFalse (reverseOn 3 0 (by decide)))

 theorem replaceFalse_executes (g : BitString → ℕ) (b : Bool) (rest rev : BitString) :
    replaceFalse.Executes g (coinStore (b::rest) [] [] rev) (coinStore (false::rest) [] [] rev) 3 := by
  have hp : (push (0 : Fin 4) false).Executes g (coinStore rest [] [] rev) (coinStore (false::rest) [] [] rev) 1 := by
    convert push_executes g (0 : Fin 4) false (coinStore rest [] [] rev) using 1
    funext i; fin_cases i <;> rfl
  have hs : Function.update (coinStore (b::rest) [] [] rev) (0 : Fin 4) rest=coinStore rest [] [] rev := by
    funext i; fin_cases i <;> rfl
  cases b with
  | false => exact branchPop_false _ _ _ _ g rfl (by rw [hs]; exact hp)
  | true => exact branchPop_true _ _ _ _ g rfl (by rw [hs]; exact hp)

/-- The index and temporary prefix are physically consumed; every other bit of
the mask is preserved in its original position. -/
theorem clearAt_executes (g : BitString → ℕ) (pre rest : BitString) (b : Bool) :
    clearAt.Executes g (coinStore (pre++b::rest) (List.replicate pre.length true) [] [])
      (coinStore (pre++false::rest) [] [] []) (7*pre.length+9) := by
  have hl : takeCoinsLoop.Executes g
      (coinStore (pre++b::rest) (List.replicate pre.length true) [] [])
      (coinStore (b::rest) [] [] pre.reverse) (5*pre.length+1) := by
    simpa using whilePop_executes _ _ _ g (takeCoinsLoop_execution g pre (b::rest) [])
  have hc := replaceFalse_executes g b rest pre.reverse
  have hr : (reverseOn (3 : Fin 4) 0 (by decide)).Executes g
      (coinStore (false::rest) [] [] pre.reverse) (coinStore (pre++false::rest) [] [] []) (2*pre.length+1) := by
    convert reverseOn_executes g (3 : Fin 4) 0 (by decide) (coinStore (false::rest) [] [] pre.reverse) using 1
    · funext i; fin_cases i <;> simp [coinStore]
    · simp [coinStore]
  convert seq_executes _ _ g hl (seq_executes _ _ g hc hr) using 1 <;> omega

 theorem clearAt_index (g : BitString → ℕ) (mask : BitString) (i : Fin mask.length) :
    clearAt.Executes g (coinStore mask (List.replicate i.val true) [] [])
      (coinStore (mask.set i.val false) [] [] []) (7*i.val+9) := by
  have h := clearAt_executes g (mask.take i.val) (mask.drop (i.val+1)) (mask.get i)
  have hin : mask.take i.val ++ mask.get i :: mask.drop (i.val+1)=mask := by
    rw [List.get_eq_getElem,List.getElem_cons_drop,List.take_append_drop]
  have hout : mask.take i.val ++ false :: mask.drop (i.val+1)=mask.set i.val false := by
    rw [List.set_eq_take_append_cons_drop,if_pos i.isLt]
  rw [hin,hout] at h
  simpa [List.length_take,Nat.min_eq_left (Nat.le_of_lt i.isLt)] using h

 theorem clearAt_queryFree : clearAt.QueryFree :=
  seq_queryFree _ _ (whilePop_queryFree _ _ _
    (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _))
    (branchPop_queryFree _ _ _ _ (push_queryFree _ _) (push_queryFree _ _) (push_queryFree _ _)))
    (seq_queryFree _ _ (branchPop_queryFree _ _ _ _ skip_queryFree (push_queryFree _ _) (push_queryFree _ _))
      (reverseOn_queryFree _ _ _))

end HiddenCircuits.Approximation.SelfReduction.Runtime
