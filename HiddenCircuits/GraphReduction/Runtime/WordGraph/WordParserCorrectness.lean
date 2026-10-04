import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParser

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParser
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 800000

theorem program_raw (g : BitString → ℕ) (p : ℕ) (S T : BitString) (ws : List BitString) (sample : BitString) :
    let input := pairBits (List.replicate p true) (encodeBitList (S::T::ws))
    ∃c, program.Executes g (store input [] [] [] [] [] sample)
      (store input (List.replicate p true) S T (encodeBitList ws) (List.replicate ws.length true) sample) c ∧
      c≤40*input.length+100 := by
  let input := pairBits (List.replicate p true) (encodeBitList (S::T::ws))
  let a := store input [] [] [] input [] sample
  let b := store input (List.replicate p true) [] [] (encodeBitList (S::T::ws)) [] sample
  let c := store input (List.replicate p true) S [] (encodeBitList (T::ws)) [] sample
  let d := store input (List.replicate p true) S T (encodeBitList ws) [] sample
  let e := store input (List.replicate p true) S T (encodeBitList ws) (List.replicate ws.length true) sample
  have h₁ : (copyOn (0:Fin 18) 4 7 (by decide) (by decide) (by decide)).Executes g
      (store input [] [] [] [] [] sample) a (5*input.length+2) := by
    convert copyOn_executes g (0:Fin 18) 4 7 (by decide) (by decide) (by decide) (store input [] [] [] [] [] sample) rfl using 1
    funext i;fin_cases i <;> simp [a,store]
  have h₂ : (parse 1).Executes g a b (5*p+7) := by
    convert parse_executes g 1 a b (List.replicate p true) (encodeBitList (S::T::ws))
      (by funext i;fin_cases i <;> rfl)
      (by funext i;fin_cases i <;> rfl)
      (by intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim) using 1
    simp only [List.length_replicate]
  have h₃ : (listHead 2).Executes g b c (5*S.length+9) := by
    apply head_executes g 2 b c S (encodeBitList (T::ws)) rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  have h₄ : (listHead 3).Executes g c d (5*T.length+9) := by
    apply head_executes g 3 c d T (encodeBitList ws) rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · intro i hi;fin_cases i <;> first | rfl | exact (hi 0 rfl).elim | exact (hi 1 rfl).elim
  obtain ⟨n,hn,hnb⟩ := Circuit.Runtime.WordCount.on_executes countEmbedding g d ws
    (by funext i;fin_cases i <;> rfl)
  have he : Function.update d (countEmbedding 5) (List.replicate ws.length true)=e := by
    funext i;fin_cases i <;> rfl
  rw [he] at hn
  refine ⟨_,seq_executes _ _ g h₁ (seq_executes _ _ g h₂ (seq_executes _ _ g h₃ (seq_executes _ _ g h₄ hn))),?_⟩
  have hlen : input.length=2*p+2*S.length+2*T.length+(encodeBitList ws).length+5 := by
    simp only [input,pairBits_length,List.length_replicate,encodeBitList,List.length_cons]
    omega
  simp only [Circuit.Runtime.WordCount.time,eval_add,eval_mul,eval_X,eval_ofNat] at hnb
  change _≤40*input.length+100
  omega

def state (w : WordInstance) (t : ℕ) : Store 17 := store (wordBits w) (List.replicate w.particles true)
  (stateBits w.source) (stateBits w.target) (encodeBitList (w.word.map letterBits)) (List.replicate w.word.length true) (List.replicate t true)

theorem program_executes (g : BitString → ℕ) (w : WordInstance) (t : ℕ) :
    ∃c, program.Executes g (store (wordBits w) [] [] [] [] [] (List.replicate t true)) (state w t) c ∧
      c≤40*(wordBits w).length+100 := by
  simpa only [state,wordBits,List.length_map] using
    program_raw g w.particles (stateBits w.source) (stateBits w.target) (w.word.map letterBits) (List.replicate t true)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.WordParser
