import HiddenCircuits.Circuit.Runtime.SpectralTableData

/-! A unary-driven finite loop emits the actual initial zero coefficient vector. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralZeroVector
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

def state (clock out : BitString) : Store 1 := fun i => if i.val=0 then clock else out
noncomputable def body : OracleBlock 1 := prepend 1 (wordChunk (signedBits 0))
noncomputable def program : OracleBlock 1 := whilePop 0 body body

 theorem loop_executes (oracle : BitString → ℕ) (n : ℕ) (out : BitString) :
    WhileExecution (0:Fin 2) body body oracle (state (List.replicate n true) out)
      (state [] (encodeBitList (List.replicate n (signedBits 0))++out)) (15*n+1) := by
  induction n generalizing out with
  | zero => simpa [encodeBitList,state] using (WhileExecution.empty (stack:=(0:Fin 2)) (B:=body) (C:=body)
      (g:=oracle) (state [] out) rfl)
  | succ n ih =>
    have hb : body.Executes oracle (state (List.replicate n true) out)
        (state (List.replicate n true) (wordChunk (signedBits 0)++out)) 13 := by
      convert prepend_executes oracle (1:Fin 2) (wordChunk (signedBits 0)) (state (List.replicate n true) out) using 1
      funext i;fin_cases i <;> rfl
    have he : Function.update (state (List.replicate (n+1) true) out) (0:Fin 2) (List.replicate n true)=
        state (List.replicate n true) out := by funext i;fin_cases i <;> rfl
    have hh := WhileExecution.one (show state (List.replicate (n+1) true) out 0=true::List.replicate n true from rfl)
      (by rw [he];exact hb) (ih (wordChunk (signedBits 0)++out))
    convert hh using 1
    · congr 1
      rw [List.replicate_succ',encodeBitList_append]
      simp [encodeBitList_eq_chunks,List.append_assoc]
    · omega

 theorem program_executes (oracle : BitString → ℕ) (n : ℕ) :
    program.Executes oracle (state (List.replicate n true) [])
      (state [] (encodeBitList ((List.replicate n (0:ℤ)).map signedBits))) (15*n+1) := by
  simpa only [List.map_replicate,List.append_nil] using whilePop_executes _ _ _ oracle (loop_executes oracle n [])

 theorem program_queryFree : program.QueryFree := whilePop_queryFree _ _ _ (prepend_queryFree _ _) (prepend_queryFree _ _)
end HiddenCircuits.Circuit.Runtime.SpectralZeroVector
