import HiddenCircuits.Circuit.Runtime.BoundaryMask
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit
import HiddenCircuits.Complexity.OracleRepeat

namespace HiddenCircuits.Circuit.Runtime.BoundaryMask
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

def store (n : ℕ) (out clock mask word : BitString) : Store 5 := fun i =>
  if i.val=0 then List.replicate n true else if i.val=1 then out else if i.val=2 then clock
  else if i.val=3 then mask else if i.val=4 then word else []
def emitEmbedding : Fin 2 ↪ Fin 6 where
  toFun i := if i.val=0 then 4 else 1
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def emit : OracleBlock 5 := rename wordEmit emitEmbedding
noncomputable def copyMask : OracleBlock 5 := copyOn 3 4 5 (by decide) (by decide) (by decide)
noncomputable def prepare : OracleBlock 5 := seq (copyOn 0 2 5 (by decide) (by decide) (by decide))
  (repeatPrepend 2 3 [true,false,true,false])
noncomputable def emitMask : OracleBlock 5 := seq copyMask emit
noncomputable def program : OracleBlock 5 := seq prepare (seq emitMask (seq emitMask (clear 3)))

theorem prepare_executes (oracle : BitString → ℕ) (n : ℕ) (out : BitString) :
    prepare.Executes oracle (store n out [] [] []) (store n out [] (mask n) []) (20*n+5) := by
  have hc : (copyOn (0:Fin 6) 2 5 (by decide) (by decide) (by decide)).Executes oracle
      (store n out [] [] []) (store n out (List.replicate n true) [] []) (5*n+2) := by
    convert copyOn_executes oracle (0:Fin 6) 2 5 (by decide) (by decide) (by decide) (store n out [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hr : (repeatPrepend (2:Fin 6) 3 [true,false,true,false]).Executes oracle
      (store n out (List.replicate n true) [] []) (store n out [] (mask n) []) (15*n+1) := by
    convert repeatPrepend_executes oracle (2:Fin 6) 3 (by decide) [true,false,true,false]
      (store n out (List.replicate n true) [] []) using 1
    · funext i;fin_cases i <;> simp [store,mask]
    · simp [store]
  convert seq_executes _ _ oracle hc hr using 1 <;> omega

theorem emitMask_executes (oracle : BitString → ℕ) (n : ℕ) (out : BitString) :
    emitMask.Executes oracle (store n out [] (mask n) [])
      (store n ((wordChunk (mask n)).reverse++out) [] (mask n) []) (44*n+11) := by
  have hc : copyMask.Executes oracle (store n out [] (mask n) []) (store n out [] (mask n) (mask n)) (20*n+2) := by
    convert copyOn_executes oracle (3:Fin 6) 4 5 (by decide) (by decide) (by decide) (store n out [] (mask n) []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store];omega
  have he : emit.Executes oracle (store n out [] (mask n) (mask n))
      (store n ((wordChunk (mask n)).reverse++out) [] (mask n) []) (24*n+7) := by
    have hh := wordEmit_executes oracle (mask n) out
    rw [mask_length] at hh
    have hr := rename_executes_to wordEmit emitEmbedding oracle hh
      (outerS:=store n out [] (mask n) (mask n))
      (outerT:=store n ((wordChunk (mask n)).reverse++out) [] (mask n) [])
      (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl))
    convert hr using 1 <;> omega
  convert seq_executes _ _ oracle hc he using 1 <;> omega

theorem program_executes (oracle : BitString → ℕ) (n : ℕ) (out : BitString) :
    program.Executes oracle (store n out [] [] [])
      (store n ((encodeBitList [mask n,mask n]).reverse++out) [] [] []) (112*n+34) := by
  have h₁ := prepare_executes oracle n out
  have h₂ := emitMask_executes oracle n out
  have h₃ := emitMask_executes oracle n ((wordChunk (mask n)).reverse++out)
  have hc : (clear (3:Fin 6)).Executes oracle
      (store n ((wordChunk (mask n)).reverse++((wordChunk (mask n)).reverse++out)) [] (mask n) [])
      (store n ((wordChunk (mask n)).reverse++((wordChunk (mask n)).reverse++out)) [] [] []) (4*n+1) := by
    convert clear_executes oracle (3:Fin 6) (store n ((wordChunk (mask n)).reverse++((wordChunk (mask n)).reverse++out)) [] (mask n) []) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  convert seq_executes _ _ oracle h₁ (seq_executes _ _ oracle h₂ (seq_executes _ _ oracle h₃ hc)) using 1
  · simp [encodeBitList_eq_chunks,List.reverse_append,List.append_assoc]
  · omega

theorem program_queryFree : program.QueryFree :=
  seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (repeatPrepend_queryFree _ _ _))
    (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ wordEmit_queryFree))
      (seq_queryFree _ _ (seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (rename_queryFree _ _ wordEmit_queryFree)) (clear_queryFree _)))
end HiddenCircuits.Circuit.Runtime.BoundaryMask
