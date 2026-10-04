import HiddenCircuits.Complexity.BinaryArithmetic.Subtraction
import HiddenCircuits.Complexity.OracleLibrary
import HiddenCircuits.Complexity.OracleBlockNoQuery

/-! Normalize a reversed unsigned word by dropping leading zeros
and physically reversing the remaining suffix. Only two stacks are used. -/
namespace HiddenCircuits.Approximation.Initialization.NormalizeReversed
open Complexity Complexity.OracleBlock Complexity.BinaryArithmetic

def state (source out : BitString) : Store 1 := fun i => if i.val=0 then source else out
noncomputable def accept : OracleBlock 1 := seq (push 1 true) (reverseOn 0 1 (by decide))
noncomputable def program : OracleBlock 1 := whilePop 0 skip accept

theorem accept_executes (g : BitString → ℕ) (xs : BitString) :
    accept.Executes g (state xs []) (state [] (xs.reverse++[true])) (2*xs.length+4) := by
  have hp : (push (1 : Fin 2) true).Executes g (state xs []) (state xs [true]) 1 := by
    convert push_executes g (1 : Fin 2) true _ using 1
    funext r; fin_cases r <;> rfl
  have hr : (reverseOn (0 : Fin 2) 1 (by decide)).Executes g
      (state xs [true]) (state [] (xs.reverse++[true])) (2*xs.length+1) := by
    convert reverseOn_executes g (0 : Fin 2) 1 (by decide) _ using 1
    funext r; fin_cases r <;> simp [state]
  convert seq_executes _ _ g hp hr using 1 <;> omega

theorem program_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ t, program.Executes g (state xs []) (state [] (normalize xs.reverse)) t ∧
      t ≤ 3*xs.length+4 := by
  have hh : ∃ t, WhileExecution (0 : Fin 2) skip accept g (state xs [])
      (state [] (normalize xs.reverse)) t ∧ t ≤ 3*xs.length+4 := by
    induction xs with
    | nil => exact ⟨1,WhileExecution.empty _ rfl,by simp⟩
    | cons b xs ih =>
      have hpop : Function.update (state (b::xs) []) 0 xs = state xs [] := by
        funext r; fin_cases r <;> rfl
      cases b with
      | false =>
        obtain ⟨t,ht,hb⟩ := ih
        refine ⟨1+1+1+t,?_,by simp; omega⟩
        rw [normalize_reverse_false]
        exact WhileExecution.zero rfl (by rw [hpop];exact skip_executes g _) ht
      | true =>
        refine ⟨1+(2*xs.length+4)+1+1,?_,by simp; omega⟩
        rw [normalize_reverse_true]
        exact WhileExecution.one rfl (by rw [hpop];exact accept_executes g xs)
          (WhileExecution.empty _ rfl)
  obtain ⟨t,ht,hb⟩ := hh
  exact ⟨t,whilePop_executes _ _ _ g ht,hb⟩

theorem canonical_executes (g : BitString → ℕ) (xs : BitString) :
    ∃ t, program.Executes g (state xs.reverse [])
      (state [] (Computability.encodeNat (value xs))) t ∧ t ≤ 3*xs.length+4 := by
  simpa only [List.reverse_reverse,normalize_eq_encode,List.length_reverse] using program_executes g xs.reverse

theorem program_queryFree : program.QueryFree :=
  whilePop_queryFree _ _ _ skip_queryFree
    (seq_queryFree _ _ (push_queryFree _ _) (reverseOn_queryFree _ _ _))

end HiddenCircuits.Approximation.Initialization.NormalizeReversed
