import HiddenCircuits.Complexity.EvalValidation.Prepare
import HiddenCircuits.GraphReduction.Runtime.LocalCleanup

namespace HiddenCircuits.Complexity.EvalValidation.Finish
open OracleBlock GraphVerifier.Runtime Core
set_option maxHeartbeats 1000000

def headerPorts : Fin 4 ↪ Fin 32 where
  toFun i:=![4,10,11,6] i
  inj' := by decide +kernel
def cleanupPorts : List (Fin 32) := (List.finRange 32).filter (fun i=>decide (i≠0 ∧ i≠6))
noncomputable def select : OracleBlock 31 := branchPop 6 skip skip (push 1 true)
noncomputable def program : OracleBlock 31 := seq (headerOn headerPorts) (seq (clearList cleanupPorts) select)
def ready (input : BitString) (b : Bool) : Store 31 := Function.update (Function.update (fun _=>[]) 0 input) 6 [b]
def output (input : BitString) (b : Bool) : Store 31 := Function.update (Function.update (fun _=>[]) 0 input) 1 (if b then [true] else [])
lemma select_executes (g : BitString→ℕ) (input : BitString) (b : Bool) :
    select.Executes g (ready input b) (output input b) 3 := by
  have he:Function.update (ready input b) 6 []=Function.update (fun _=>[]) 0 input := by
    funext i;fin_cases i <;> rfl
  cases b
  · apply branchPop_false 6 _ _ _ g rfl
    rw [he]
    convert skip_executes g (Function.update (fun _=>[]) (0:Fin 32) input) using 1
    funext i;fin_cases i <;> rfl
  · apply branchPop_true 6 _ _ _ g rfl
    rw [he]
    exact push_executes g (1:Fin 32) true (Function.update (fun _=>[]) 0 input)

theorem program_executes (g : BitString→ℕ) (input data p width flags : BitString) (B : ℕ)
    (hB:∀i,(state input data p width flags [] [] i).length≤B) :
    ∃c,program.Executes g (state input data p width flags [] []) (output input (flags.all id)) c ∧ c≤300*(B+1) := by
  let start:=state input data p width flags [] []
  let mid:=Function.update (Function.update start (10:Fin 32) (List.replicate flags.length true)) 6 [flags.all id]
  have hh:(headerOn headerPorts).Executes g start mid (5*flags.length+3) :=
    headerOn_executes headerPorts g start flags (by funext i;fin_cases i <;> rfl)
  have hs:∀i : Fin 32,(mid i).length≤B+(5*flags.length+3):=hh.stack_bound hB
  obtain ⟨c,hc,hcb⟩:=clearList_executes g cleanupPorts mid (B+(5*flags.length+3)) hs
  have he:eraseStore cleanupPorts mid=ready input (flags.all id) := by
    funext i;fin_cases i <;> simp [eraseStore,cleanupPorts,mid,start,state,ready]
  rw [he] at hc
  refine ⟨_,seq_executes _ _ g hh (seq_executes _ _ g hc (select_executes g input (flags.all id))),?_⟩
  have hf:flags.length≤B:=hB 4
  have hl:cleanupPorts.length≤32:=(List.length_filter_le _ _).trans (by simp)
  have hc':=hcb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1)
  omega
end HiddenCircuits.Complexity.EvalValidation.Finish
