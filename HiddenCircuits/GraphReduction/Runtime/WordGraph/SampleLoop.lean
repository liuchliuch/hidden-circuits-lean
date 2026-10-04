import HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleParse

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 700000
noncomputable def loop : OracleBlock 17 := whilePop 7 body body

lemma pop_stream (w : WordInstance) (t : ℕ) (b : Bool) (rest out : BitString) (h : ℕ) :
    Function.update (state w t (b::rest) [] [] out h) 7 rest=state w t rest [] [] out h := by
  funext i;fin_cases i <;> rfl

theorem loop_execution (g : BitString → ℕ) (w : WordInstance) (ls : List (Letter (2*w.particles)))
    (t : ℕ) (out : BitString) (h : ℕ) :
    ∃c,WhileExecution (7:Fin 18) body body g (state w t (encodeBitList (ls.map letterBits)) [] [] out h)
      (state w t [] [] [] ((pairStream (sampleWord ls t)).reverse++out) (h+ls.length*(t+1))) c ∧
      c≤ls.length*(34*w.particles+41*t+122)+1 := by
  induction ls generalizing h out with
  | nil => exact ⟨1,by simpa [sampleWord] using WhileExecution.empty (stack:=(7:Fin 18)) (B:=body) (C:=body) (g:=g) (state w t [] [] [] out h) rfl,by simp⟩
  | cons l ls ih =>
    obtain ⟨c,hc,hb⟩ := ih ((pairStream (sampleLetter l t)).reverse++out) (h+t+1)
    have he := body_executes g w l t (encodeBitList (ls.map letterBits)) out h
    have hs := WhileExecution.one (stack:=(7:Fin 18)) (B:=body) (C:=body) (g:=g)
      (s:=state w t (encodeBitList ((l::ls).map letterBits)) [] [] out h) rfl
      (by rw [List.map_cons,encodeBitList,pop_stream];exact he) hc
    refine ⟨1+(17*l.index.val+41*t+120)+1+c,?_,?_⟩
    · convert hs using 1
      simp only [sampleWord,List.flatMap_cons,pairStream_append,List.reverse_append,List.append_assoc,List.length_cons]
      congr 1
      ring
    · have hl : l.index.val≤2*w.particles := by have := l.index.isLt;omega
      simp only [List.length_cons]
      nlinarith
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
