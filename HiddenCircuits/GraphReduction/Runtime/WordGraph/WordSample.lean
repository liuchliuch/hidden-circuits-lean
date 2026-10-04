import HiddenCircuits.GraphReduction.Runtime.WordGraph.SampleLoop

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
open Complexity OracleBlock BinaryArithmetic
set_option maxHeartbeats 700000
noncomputable def afterParse : OracleBlock 17 := seq (copyOn 4 7 10 (by decide) (by decide) (by decide))
  (seq loop (reverseOn 14 12 (by decide)))
noncomputable def program : OracleBlock 17 := seq WordParser.program afterParse

def output (w : WordInstance) (t : ℕ) : Store 17 :=
  state w t [] [] [] [] (sampleWord w.word t).length (pairStream (sampleWord w.word t))

theorem afterParse_executes (g : BitString → ℕ) (w : WordInstance) (t : ℕ) :
    ∃c,afterParse.Executes g (WordParser.state w t) (output w t) c ∧
      c≤5*(encodeBitList (w.word.map letterBits)).length+w.word.length*(34*w.particles+41*t+122)+
        2*(pairStream (sampleWord w.word t)).length+8 := by
  let E := encodeBitList (w.word.map letterBits)
  have hc : (copyOn (4:Fin 18) 7 10 (by decide) (by decide) (by decide)).Executes g (WordParser.state w t)
      (state w t E [] [] [] 0) (5*E.length+2) := by
    convert copyOn_executes g (4:Fin 18) 7 10 (by decide) (by decide) (by decide) (WordParser.state w t) rfl using 1
    funext i;fin_cases i <;> simp [state,WordParser.state,WordParser.store,E]
  obtain ⟨c,hl,hb⟩ := loop_execution g w w.word t [] 0
  simp only [Nat.zero_add,List.append_nil,←sampleWord_length] at hl
  have hr : (reverseOn (14:Fin 18) 12 (by decide)).Executes g
      (state w t [] [] [] (pairStream (sampleWord w.word t)).reverse (sampleWord w.word t).length)
      (output w t) (2*(pairStream (sampleWord w.word t)).length+1) := by
    convert reverseOn_executes g (14:Fin 18) 12 (by decide)
      (state w t [] [] [] (pairStream (sampleWord w.word t)).reverse (sampleWord w.word t).length) using 1
    · funext i;fin_cases i <;> simp [output,state,List.reverse_reverse]
    · simp [state]
  exact ⟨_,seq_executes _ _ g hc (seq_executes _ _ g (whilePop_executes _ _ _ g hl) hr),by dsimp only [E] at *;omega⟩

theorem program_executes (g : BitString → ℕ) (w : WordInstance) (t : ℕ) :
    ∃c,program.Executes g (WordParser.store (wordBits w) [] [] [] [] [] (List.replicate t true)) (output w t) c ∧
      c≤40*(wordBits w).length+5*(encodeBitList (w.word.map letterBits)).length+
        w.word.length*(34*w.particles+41*t+122)+2*(pairStream (sampleWord w.word t)).length+110 := by
  obtain ⟨a,ha,hab⟩ := WordParser.program_executes g w t
  obtain ⟨b,hb,hbb⟩ := afterParse_executes g w t
  exact ⟨_,seq_executes _ _ g ha hb,by omega⟩
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSample
