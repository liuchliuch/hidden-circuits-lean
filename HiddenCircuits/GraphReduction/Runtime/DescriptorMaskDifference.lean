import HiddenCircuits.GraphReduction.Runtime.DescriptorMaskRow

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorMaskDifference
open Complexity OracleBlock
set_option maxHeartbeats 500000

def difference (xs ys : BitString) : BitString := List.zipWith (fun a b => a && !b) xs ys
def state (left right reverseOut result : BitString) : Store 3 := ![left,right,reverseOut,result]
noncomputable def step (b : Bool) : OracleBlock 3 := branchPop 1 skip (push 2 b) (push 2 false)
noncomputable def loop : OracleBlock 3 := whilePop 0 (step false) (step true)
noncomputable def program : OracleBlock 3 := seq loop (reverseOn 2 3 (by decide))

lemma step_executes (g : BitString → ℕ) (a b : Bool) (xs ys out : BitString) :
    (step a).Executes g (state xs (b::ys) out []) (state xs ys ((a && !b)::out) []) 3 := by
  have hu : Function.update (state xs (b::ys) out []) (1:Fin 4) ys=state xs ys out [] := by
    funext i;fin_cases i <;> rfl
  have hp : (push (2:Fin 4) (a && !b)).Executes g (state xs ys out []) (state xs ys ((a && !b)::out) []) 1 := by
    convert push_executes g (2:Fin 4) (a && !b) (state xs ys out []) using 1
    funext i;fin_cases i <;> rfl
  cases b
  · apply branchPop_false 1 skip (push 2 a) (push 2 false) g rfl
    rw [hu]
    simpa only [Bool.not_false,Bool.and_true] using hp
  · apply branchPop_true 1 skip (push 2 a) (push 2 false) g rfl
    rw [hu]
    simpa only [Bool.not_true,Bool.and_false] using hp

lemma loop_execution (g : BitString → ℕ) (xs ys out : BitString) (hlen : xs.length=ys.length) :
    WhileExecution (0:Fin 4) (step false) (step true) g (state xs ys out [])
      (state [] [] ((difference xs ys).reverse++out) []) (5*xs.length+1) := by
  induction xs generalizing ys out with
  | nil =>
    have hy : ys=[] := by cases ys <;> simp_all
    subst ys
    exact WhileExecution.empty _ rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have ht : xs.length=ys.length := by simpa using hlen
      have hu : Function.update (state (a::xs) (b::ys) out []) (0:Fin 4) xs=state xs (b::ys) out [] := by
        funext i;fin_cases i <;> rfl
      have hp := step_executes g a b xs ys out
      rw [←hu] at hp
      have hh := ih ys ((a && !b)::out) ht
      cases a
      · have he := WhileExecution.zero (stack:=(0:Fin 4)) (B:=step false) (C:=step true) (g:=g) rfl hp hh
        convert he using 1 <;> simp [difference,List.reverse_cons,List.append_assoc] <;> omega
      · have he := WhileExecution.one (stack:=(0:Fin 4)) (B:=step false) (C:=step true) (g:=g) rfl hp hh
        convert he using 1 <;> simp [difference,List.reverse_cons,List.append_assoc] <;> omega

@[simp] lemma difference_length (xs ys : BitString) (hlen : xs.length=ys.length) : (difference xs ys).length=xs.length := by
  simp [difference,hlen]

theorem program_executes (g : BitString → ℕ) (xs ys : BitString) (hlen : xs.length=ys.length) :
    program.Executes g (state xs ys [] []) (state [] [] [] (difference xs ys)) (7*xs.length+4) := by
  have hl := whilePop_executes _ _ _ g (loop_execution g xs ys [] hlen)
  simp only [List.append_nil] at hl
  have hr : (reverseOn (2:Fin 4) 3 (by decide)).Executes g (state [] [] (difference xs ys).reverse [])
      (state [] [] [] (difference xs ys)) (2*xs.length+1) := by
    convert reverseOn_executes g (2:Fin 4) 3 (by decide) (state [] [] (difference xs ys).reverse []) using 1
    · funext i;fin_cases i <;> simp [state]
    · simp [state,difference_length xs ys hlen]
  convert seq_executes _ _ g hl hr using 1 <;> omega

lemma program_queryFree : program.QueryFree := seq_queryFree _ _
  (whilePop_queryFree _ _ _ (branchPop_queryFree _ _ _ _ skip_queryFree (push_queryFree _ _) (push_queryFree _ _))
    (branchPop_queryFree _ _ _ _ skip_queryFree (push_queryFree _ _) (push_queryFree _ _))) (reverseOn_queryFree _ _ _)
end HiddenCircuits.GraphReduction.Runtime.DescriptorMaskDifference
