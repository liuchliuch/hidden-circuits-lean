import HiddenCircuits.Complexity.GraphVerifier.RuntimeLibrary

/-! Unary clock multiplication by an actual finite repeated-copy loop. -/
namespace HiddenCircuits.Complexity.GraphVerifier.Runtime
open OracleBlock

def repeatPrefix (a : BitString) : ℕ → BitString → BitString
  | 0,out => out
  | n+1,out => repeatPrefix a n (a++out)

noncomputable def repeatCopyBody : OracleBlock 3 := copyOn 0 2 3 (by decide) (by decide) (by decide)
noncomputable def repeatCopyBlock : OracleBlock 3 := whilePop 1 repeatCopyBody repeatCopyBody

def repeatCopyStore (a counter out : BitString) : Store 3 :=
  Fin.cases a (Fin.cases counter (Fin.cases out (fun _ => [])))

 theorem repeatCopy_body (g : BitString → ℕ) (a counter out : BitString) :
    repeatCopyBody.Executes g (repeatCopyStore a counter out) (repeatCopyStore a counter (a++out))
      (5*a.length+2) := by
  have h := copyOn_executes g (0:Fin 4) 2 3 (by decide) (by decide) (by decide)
    (repeatCopyStore a counter out) rfl
  have he : Function.update (repeatCopyStore a counter out) (2:Fin 4) (a++out)=
      repeatCopyStore a counter (a++out) := by funext i; fin_cases i <;> rfl
  change repeatCopyBody.Executes g (repeatCopyStore a counter out)
    (Function.update (repeatCopyStore a counter out) (2:Fin 4) (a++out)) (5*a.length+2) at h
  rw [he] at h
  exact h

 theorem repeatCopy_execution (g : BitString → ℕ) (a counter out : BitString) :
    repeatCopyBlock.Executes g (repeatCopyStore a counter out)
      (repeatCopyStore a [] (repeatPrefix a counter.length out))
      (counter.length*(5*a.length+4)+1) := by
  apply whilePop_executes
  induction counter generalizing out with
  | nil => simpa only [List.length_nil,repeatPrefix,Nat.zero_mul,Nat.zero_add] using
      WhileExecution.empty (stack:=(1:Fin 4)) (B:=repeatCopyBody) (C:=repeatCopyBody) (g:=g) (repeatCopyStore a [] out) rfl
  | cons b counter ih =>
    have he : Function.update (repeatCopyStore a (b::counter) out) (1:Fin 4) counter=
        repeatCopyStore a counter out := by funext i; fin_cases i <;> rfl
    have hbody : repeatCopyBody.Executes g
        (Function.update (repeatCopyStore a (b::counter) out) (1:Fin 4) counter)
        (repeatCopyStore a counter (a++out)) (5*a.length+2) := by rw [he]; exact repeatCopy_body g a counter out
    have ht := ih (a++out)
    cases b with
    | false =>
      have hh := WhileExecution.zero (stack:= (1:Fin 4)) rfl hbody ht
      convert hh using 1 <;> simp only [List.length_cons,repeatPrefix] <;> ring
    | true =>
      have hh := WhileExecution.one (stack:= (1:Fin 4)) rfl hbody ht
      convert hh using 1 <;> simp only [List.length_cons,repeatPrefix] <;> ring

 theorem repeatPrefix_unary (n m k : ℕ) :
    repeatPrefix (List.replicate n true) m (List.replicate k true)=List.replicate (m*n+k) true := by
  induction m generalizing k with
  | zero => simp [repeatPrefix]
  | succ m ih =>
    rw [repeatPrefix,← List.replicate_add,ih]
    congr 1
    ring

/-- This is a real finite bit program whose quadratic charge covers every copied unary cell. -/
theorem unaryProduct_execution (g : BitString → ℕ) (n m : ℕ) :
    repeatCopyBlock.Executes g (repeatCopyStore (List.replicate n true) (List.replicate m true) [])
      (repeatCopyStore (List.replicate n true) [] (List.replicate (m*n) true))
      (m*(5*n+4)+1) := by
  have hh := repeatCopy_execution g (List.replicate n true) (List.replicate m true) []
  simpa only [List.length_replicate,show ([]:BitString)=List.replicate 0 true from rfl,
    repeatPrefix_unary,Nat.add_zero] using hh

 theorem repeatCopy_queryFree : repeatCopyBlock.QueryFree :=
  whilePop_queryFree _ _ _ (copyOn_queryFree _ _ _ _ _ _) (copyOn_queryFree _ _ _ _ _ _)

end HiddenCircuits.Complexity.GraphVerifier.Runtime
