import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCellWeights
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

lemma norm_executes (g : BitString → ℕ) (t k s l p h : ℕ) (answer dt nt ds ns : BitString) :
    ∃c, norm.Executes g (state t k s l p h answer [] [] (fields dt nt ds ns [] [] []))
      (state t k s l p h answer [] []
        (fields dt nt ds ns (signedBits ((s.factorial:ℤ)^h)) (signedBits ((-1:ℤ)^(p*h))) [])) c ∧
      c≤RatioNormalization.time.eval (s+h+p) := by
  obtain ⟨c,hc,hb⟩ := RatioNormalization.program_executes g s h p
  refine ⟨c,?_,hb⟩
  apply rename_executes_to RatioNormalization.program normEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h13 : i.val≠13 := by intro h;exact hi 3 (Fin.ext h.symm)
    have h14 : i.val≠14 := by intro h;exact hi 4 (Fin.ext h.symm)
    simp only [state,fields,h13,h14,if_false]

lemma copyAnswer_executes (g : BitString → ℕ) (t k s l p h : ℕ) (answer dt nt ds ns factor sign : BitString) :
    copyAnswer.Executes g (state t k s l p h answer [] [] (fields dt nt ds ns factor sign []))
      (state t k s l p h answer [] [] (fields dt nt ds ns factor sign answer)) (5*answer.length+2) := by
  convert copyOn_executes g (6:Fin 53) 15 16 (by decide) (by decide) (by decide)
    (state t k s l p h answer [] [] (fields dt nt ds ns factor sign [])) rfl using 1
  funext i;fin_cases i <;> simp [state,fields]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
