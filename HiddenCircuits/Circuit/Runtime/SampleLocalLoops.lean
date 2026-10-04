import HiddenCircuits.Circuit.Runtime.LetterEmitterFixed
import HiddenCircuits.Circuit.SampleWords

/-! Finite local physical-word emission and unary-clock repetition for the
sampled constraint compiler. Scalar metadata is preserved by these loops. -/
namespace HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
open HiddenCircuits.Complexity OracleBlock

/-- Base0 and sample1 are preserved, stream2 grows in reverse order,
exponent3/sign4 are framed, and work5–8 is cleared. -/
def store (p u clock : ℕ) (stream exponent sign counter temporary work : BitString) : Store 8 := fun i =>
  if i.val=0 then List.replicate p true else if i.val=1 then List.replicate u true else if i.val=2 then stream
  else if i.val=3 then exponent else if i.val=4 then sign else if i.val=5 then counter
  else if i.val=6 then temporary else if i.val=7 then List.replicate clock true else work

def letterEmbedding : Fin 4 ↪ Fin 9 where
  toFun i := (![0,2,5,6] : Fin 4 → Fin 9) i
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

noncomputable def fixed {n : ℕ} (w : List (Letter n)) : OracleBlock 8 :=
  LetterEmitter.fixedWordOn letterEmbedding w
noncomputable def repeated {n : ℕ} (w : List (Letter n)) : OracleBlock 8 :=
  whilePop 7 (fixed w) (fixed w)
noncomputable def repeatSample {n : ℕ} (w : List (Letter n)) : OracleBlock 8 :=
  seq (copyOn 1 7 8 (by decide) (by decide) (by decide)) (repeated w)

def repeatedBits {n : ℕ} (p count : ℕ) (w : List (Letter n)) : BitString :=
  (List.replicate count (LetterEmitter.wordBitsAt p w)).flatten

theorem fixed_executes {n : ℕ} (g : BitString → ℕ) (w : List (Letter n)) (p u clock : ℕ)
    (out exponent sign : BitString) :
    (fixed w).Executes g (store p u clock out exponent sign [] [] [])
      (store p u clock ((LetterEmitter.wordBitsAt p w).reverse++out) exponent sign [] [] [])
      (LetterEmitter.wordCost p w) := by
  apply rename_executes_to _ letterEmbedding g (LetterEmitter.fixedWord_executes g w p out)
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi;fin_cases i <;> first | rfl | exact (hi 1 rfl).elim

lemma update_clock (p u clock : ℕ) (out exponent sign : BitString) :
    Function.update (store p u (clock+1) out exponent sign [] [] []) 7 (List.replicate clock true)=
      store p u clock out exponent sign [] [] [] := by
  funext i;fin_cases i <;> rfl

lemma repeated_execution {n : ℕ} (g : BitString → ℕ) (w : List (Letter n)) (p u count : ℕ)
    (out exponent sign : BitString) :
    WhileExecution (7:Fin 9) (fixed w) (fixed w) g (store p u count out exponent sign [] [] [])
      (store p u 0 ((repeatedBits p count w).reverse++out) exponent sign [] [] [])
      (count*(LetterEmitter.wordCost p w+2)+1) := by
  induction count generalizing out with
  | zero => simpa [repeatedBits] using WhileExecution.empty (store p u 0 out exponent sign [] [] []) rfl
  | succ count ih =>
    have hb : (fixed w).Executes g
        (Function.update (store p u (count+1) out exponent sign [] [] []) 7 (List.replicate count true))
        (store p u count ((LetterEmitter.wordBitsAt p w).reverse++out) exponent sign [] [] [])
        (LetterEmitter.wordCost p w) := by
      rw [update_clock];exact fixed_executes g w p u count out exponent sign
    have ht := ih ((LetterEmitter.wordBitsAt p w).reverse++out)
    have h := WhileExecution.one (stack:=(7:Fin 9)) (B:=fixed w) (C:=fixed w) (g:=g) rfl hb ht
    convert h using 1
    · simp [repeatedBits,List.replicate_succ,List.reverse_append,List.append_assoc]
    · nlinarith

theorem repeatSample_executes {n : ℕ} (g : BitString → ℕ) (w : List (Letter n)) (p u : ℕ)
    (out exponent sign : BitString) :
    (repeatSample w).Executes g (store p u 0 out exponent sign [] [] [])
      (store p u 0 ((repeatedBits p u w).reverse++out) exponent sign [] [] [])
      (u*(LetterEmitter.wordCost p w+7)+5) := by
  have hc : (copyOn (1:Fin 9) 7 8 (by decide) (by decide) (by decide)).Executes g
      (store p u 0 out exponent sign [] [] []) (store p u u out exponent sign [] [] []) (5*u+2) := by
    convert copyOn_executes g (1:Fin 9) 7 8 (by decide) (by decide) (by decide)
      (store p u 0 out exponent sign [] [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hl := whilePop_executes _ _ _ g (repeated_execution g w p u u out exponent sign)
  convert seq_executes _ _ g hc hl using 1 <;> nlinarith

lemma fixed_queryFree {n : ℕ} (w : List (Letter n)) : (fixed w).QueryFree :=
  LetterEmitter.fixedWordOn_queryFree _ _
lemma repeated_queryFree {n : ℕ} (w : List (Letter n)) : (repeated w).QueryFree :=
  whilePop_queryFree _ _ _ (fixed_queryFree w) (fixed_queryFree w)
lemma repeatSample_queryFree {n : ℕ} (w : List (Letter n)) : (repeatSample w).QueryFree :=
  seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _) (repeated_queryFree w)

lemma update_stream (p u clock : ℕ) (out exponent sign counter temporary work next : BitString) :
    Function.update (store p u clock out exponent sign counter temporary work) 2 next=
      store p u clock next exponent sign counter temporary work := by
  funext i;fin_cases i <;> rfl

lemma wordBitsAt_append {n : ℕ} (p : ℕ) (v w : List (Letter n)) :
    LetterEmitter.wordBitsAt p (v++w)=LetterEmitter.wordBitsAt p v++LetterEmitter.wordBitsAt p w := by
  simp [LetterEmitter.wordBitsAt]
lemma wordBitsAt_repeat {n : ℕ} (p count : ℕ) (w : List (Letter n)) :
    LetterEmitter.wordBitsAt p ((List.replicate count w).flatten)=repeatedBits p count w := by
  induction count with
  | zero => simp [LetterEmitter.wordBitsAt,repeatedBits]
  | succ count ih => simp [List.replicate_succ,wordBitsAt_append,ih,repeatedBits]

end HiddenCircuits.Circuit.Runtime.SampleLocalEmitter
