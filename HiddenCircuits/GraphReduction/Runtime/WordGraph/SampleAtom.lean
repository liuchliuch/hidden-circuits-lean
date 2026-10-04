import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairEncoding
import HiddenCircuits.Complexity.OracleRepeat

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleAtom
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 700000

def state (kind index : BitString) (t : ℕ) (out : BitString) (height : ℕ) : Store 7 := fun i =>
  if i.val=0 then kind else if i.val=1 then index else if i.val=2 then List.replicate t true
  else if i.val=3 then out else if i.val=4 then List.replicate height true else []
def emitEmbedding : Fin 2 ↪ Fin 8 where
  toFun i := if i.val=0 then 5 else 3
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all
noncomputable def emit (tag : BitString) : OracleBlock 7 := seq (copyOn 1 5 7 (by decide) (by decide) (by decide))
  (seq (prepend 5 tag) (seq (rename wordEmit emitEmbedding) (push 4 true)))

theorem emit_executes (g : BitString → ℕ) (tag kind : BitString) (i t : ℕ) (out : BitString) (h : ℕ) :
    (emit tag).Executes g (state kind (List.replicate i true) t out h)
      (state kind (List.replicate i true) t ((wordChunk (tag++List.replicate i true)).reverse++out) (h+1))
      (11*i+9*tag.length+17) := by
  let s := state kind (List.replicate i true) t out h
  let a := Function.update s (5:Fin 8) (List.replicate i true)
  let b := Function.update s (5:Fin 8) (tag++List.replicate i true)
  let next := (wordChunk (tag++List.replicate i true)).reverse++out
  have hc : (copyOn (1:Fin 8) 5 7 (by decide) (by decide) (by decide)).Executes g s a (5*i+2) := by
    simpa [s,a,state] using copyOn_executes g (1:Fin 8) 5 7 (by decide) (by decide) (by decide) s rfl
  have hp : (prepend (5:Fin 8) tag).Executes g a b (3*tag.length+1) := by
    simpa only [a,b,Function.update_self,Function.update_idem] using prepend_executes g (5:Fin 8) tag a
  have he : (rename wordEmit emitEmbedding).Executes g b (state kind (List.replicate i true) t next h)
      (6*(tag.length+i)+7) := by
    have hw := wordEmit_executes g (tag++List.replicate i true) out
    simp only [List.length_append,List.length_replicate] at hw
    apply rename_executes_to wordEmit emitEmbedding g hw
    · funext j;fin_cases j <;> rfl
    · funext j;fin_cases j <;> rfl
    · intro j hj;fin_cases j <;> first | rfl | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim
  have hi : (push (4:Fin 8) true).Executes g (state kind (List.replicate i true) t next h)
      (state kind (List.replicate i true) t next (h+1)) 1 := by
    convert push_executes g (4:Fin 8) true (state kind (List.replicate i true) t next h) using 1
    funext j;fin_cases j <;> simp [state,List.replicate_succ]
  convert seq_executes _ _ g hc (seq_executes _ _ g hp (seq_executes _ _ g he hi)) using 1 <;> omega

noncomputable def background : OracleBlock 7 := seq
  (prepend 3 (wordChunk [false,false,false,false]).reverse) (push 4 true)
noncomputable def backgrounds : OracleBlock 7 := seq (copyOn 2 6 7 (by decide) (by decide) (by decide))
  (whilePop 6 background background)

def clockState (kind index : BitString) (t : ℕ) (out : BitString) (h n : ℕ) : Store 7 :=
  Function.update (state kind index t out h) 6 (List.replicate n true)

theorem background_executes (g : BitString → ℕ) (kind index : BitString) (t : ℕ) (out : BitString) (h n : ℕ) :
    background.Executes g (clockState kind index t out h n)
      (clockState kind index t ((wordChunk [false,false,false,false]).reverse++out) (h+1) n) 34 := by
  have hp : (prepend (3:Fin 8) (wordChunk [false,false,false,false]).reverse).Executes g
      (clockState kind index t out h n)
      (clockState kind index t ((wordChunk [false,false,false,false]).reverse++out) h n) 31 := by
    convert prepend_executes g (3:Fin 8) (wordChunk [false,false,false,false]).reverse (clockState kind index t out h n) using 1
    funext j;fin_cases j <;> rfl
  have hi : (push (4:Fin 8) true).Executes g
      (clockState kind index t ((wordChunk [false,false,false,false]).reverse++out) h n)
      (clockState kind index t ((wordChunk [false,false,false,false]).reverse++out) (h+1) n) 1 := by
    convert push_executes g (4:Fin 8) true (clockState kind index t ((wordChunk [false,false,false,false]).reverse++out) h n) using 1
    funext j;fin_cases j <;> simp [clockState,state,List.replicate_succ]
  exact seq_executes _ _ g hp hi

theorem backgrounds_loop (g : BitString → ℕ) (kind index : BitString) (t n : ℕ) (out : BitString) (h : ℕ) :
    WhileExecution (6:Fin 8) background background g (clockState kind index t out h n)
      (state kind index t (((List.replicate n (wordChunk [false,false,false,false])).flatten).reverse++out) (h+n)) (36*n+1) := by
  induction n generalizing h out with
  | zero =>
    have hz : clockState kind index t out h 0=state kind index t out h := by
      funext j;fin_cases j <;> rfl
    rw [hz]
    simpa using WhileExecution.empty (stack:=(6:Fin 8)) (B:=background) (C:=background)
      (g:=g) (state kind index t out h) rfl
  | succ n ih =>
    have hu : Function.update (clockState kind index t out h (n+1)) 6 (List.replicate n true)=clockState kind index t out h n := by
      simp only [clockState,Function.update_idem]
    have he := background_executes g kind index t out h n
    rw [←hu] at he
    have hs := WhileExecution.one (stack:=(6:Fin 8)) (B:=background) (C:=background) (g:=g) rfl he
      (ih ((wordChunk [false,false,false,false]).reverse++out) (h+1))
    convert hs using 1
    · simp only [List.replicate_succ,List.flatten_cons,List.reverse_append,List.append_assoc]
      congr 1
      omega
    · omega

theorem backgrounds_executes (g : BitString → ℕ) (kind index : BitString) (t : ℕ) (out : BitString) (h : ℕ) :
    backgrounds.Executes g (state kind index t out h)
      (state kind index t (((List.replicate t (wordChunk [false,false,false,false])).flatten).reverse++out) (h+t)) (41*t+5) := by
  have hc : (copyOn (2:Fin 8) 6 7 (by decide) (by decide) (by decide)).Executes g
      (state kind index t out h) (clockState kind index t out h t) (5*t+2) := by
    simpa [clockState,state] using copyOn_executes g (2:Fin 8) 6 7 (by decide) (by decide) (by decide) (state kind index t out h) rfl
  have hl := whilePop_executes _ _ _ g (backgrounds_loop g kind index t t out h)
  convert seq_executes _ _ g hc hl using 1 <;> omega

end HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleAtom
