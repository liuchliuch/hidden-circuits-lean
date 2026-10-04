import HiddenCircuits.Complexity.BinaryArithmetic.WeightRuntime
import HiddenCircuits.Complexity.BitList

/-! Literal self-delimiting signed-word emission into a reverse stream. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock

 def wordChunk (xs : BitString) : BitString := true :: pairBits xs []
 def wordPayload (xs : BitString) : BitString := xs.flatMap (fun b => [true,b])

 theorem pairBits_eq_payload (xs ys : BitString) : pairBits xs ys = wordPayload xs ++ false::ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [pairBits,wordPayload,ih]

 theorem wordChunk_eq (xs : BitString) : wordChunk xs = true :: (wordPayload xs ++ [false]) := by
  simp [wordChunk,pairBits_eq_payload]

 theorem encodeBitList_eq_chunks (xs : List BitString) : encodeBitList xs = xs.flatMap wordChunk := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeBitList,wordChunk,pairBits_eq_payload,ih,List.append_assoc]

 theorem encodeBitList_append (xs ys : List BitString) :
    encodeBitList (xs++ys) = encodeBitList xs ++ encodeBitList ys := by
  simp [encodeBitList_eq_chunks]

 def wordEmitStore (source output : BitString) : Store 1 := Fin.cases source (fun _ => output)
 noncomputable def wordEmitBit (b : Bool) : OracleBlock 1 := seq (push 1 true) (push 1 b)
 noncomputable def wordEmitLoop : OracleBlock 1 := whilePop 0 (wordEmitBit false) (wordEmitBit true)
 noncomputable def wordEmit : OracleBlock 1 := seq (push 1 true) (seq wordEmitLoop (push 1 false))

 theorem wordEmitBit_executes (g : BitString → ℕ) (b : Bool) (xs ys : BitString) :
    (wordEmitBit b).Executes g (wordEmitStore xs ys) (wordEmitStore xs (b::true::ys)) 4 := by
  have h1 : (push (1 : Fin 2) true).Executes g (wordEmitStore xs ys) (wordEmitStore xs (true::ys)) 1 := by
    convert push_executes g (1 : Fin 2) true (wordEmitStore xs ys) using 1
    funext i; fin_cases i <;> rfl
  have h2 : (push (1 : Fin 2) b).Executes g (wordEmitStore xs (true::ys)) (wordEmitStore xs (b::true::ys)) 1 := by
    convert push_executes g (1 : Fin 2) b (wordEmitStore xs (true::ys)) using 1
    funext i; fin_cases i <;> rfl
  exact seq_executes _ _ g h1 h2

 theorem wordEmitLoop_executes (g : BitString → ℕ) (xs ys : BitString) :
    wordEmitLoop.Executes g (wordEmitStore xs ys)
      (wordEmitStore [] ((wordPayload xs).reverse++ys)) (6*xs.length+1) := by
  apply whilePop_executes
  induction xs generalizing ys with
  | nil => exact WhileExecution.empty _ rfl
  | cons b xs ih =>
    have hs : Function.update (wordEmitStore (b::xs) ys) 0 xs = wordEmitStore xs ys := by
      funext i; fin_cases i <;> rfl
    have hb := wordEmitBit_executes g b xs ys
    rw [← hs] at hb
    cases b
    · have h := WhileExecution.zero rfl hb (ih (false::true::ys))
      convert h using 1 <;> simp [wordPayload,List.reverse_append,List.append_assoc] <;> omega
    · have h := WhileExecution.one rfl hb (ih (true::true::ys))
      convert h using 1 <;> simp [wordPayload,List.reverse_append,List.append_assoc] <;> omega

 theorem wordEmit_executes (g : BitString → ℕ) (xs ys : BitString) :
    wordEmit.Executes g (wordEmitStore xs ys)
      (wordEmitStore [] ((wordChunk xs).reverse++ys)) (6*xs.length+7) := by
  have h1 : (push (1 : Fin 2) true).Executes g (wordEmitStore xs ys) (wordEmitStore xs (true::ys)) 1 := by
    convert push_executes g (1 : Fin 2) true (wordEmitStore xs ys) using 1
    funext i; fin_cases i <;> rfl
  have h2 := wordEmitLoop_executes g xs (true::ys)
  have h3 : (push (1 : Fin 2) false).Executes g
      (wordEmitStore [] ((wordPayload xs).reverse++true::ys))
      (wordEmitStore [] (false::((wordPayload xs).reverse++true::ys))) 1 := by
    convert push_executes g (1 : Fin 2) false (wordEmitStore [] ((wordPayload xs).reverse++true::ys)) using 1
    funext i; fin_cases i <;> rfl
  convert seq_executes _ _ g h1 (seq_executes _ _ g h2 h3) using 1
  · simp [wordChunk_eq,List.reverse_append,List.append_assoc]
  · omega

 lemma wordEmit_queryFree : wordEmit.QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _
    (whilePop_queryFree _ _ _ (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))
      (seq_queryFree _ _ (push_queryFree _ _) (push_queryFree _ _))) (push_queryFree _ _))

end HiddenCircuits.Complexity.BinaryArithmetic
