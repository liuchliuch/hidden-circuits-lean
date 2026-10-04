import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCellDefs
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

lemma left_executes (g : BitString → ℕ) (d : ℕ) (t : Fin (d+1)) (s l p h : ℕ) (answer : BitString) :
    ∃c, left.Executes g (state t.val (d-t.val) s l p h answer [] [] (fields [] [] [] [] [] [] []))
      (state t.val (d-t.val) s l p h answer [] []
        (fields (signedBits (interpolationDenominator d t)) (signedBits (interpolationNegativeNumerator d t)) [] [] [] [] [])) c ∧
      c≤GridWeightsRuntime.pairTime.eval d := by
  obtain ⟨c,hc,hb⟩ := GridWeightsRuntime.pairProgram_executes g d t
  refine ⟨c,?_,hb⟩
  apply rename_executes_to GridWeightsRuntime.pairProgram leftEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h9 : i.val≠9 := by intro h;exact hi 2 (Fin.ext h.symm)
    have h10 : i.val≠10 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [state,fields,h9,h10,if_false]

lemma right_executes (g : BitString → ℕ) (d : ℕ) (s : Fin (d+1)) (t k p h : ℕ)
    (answer dt nt : BitString) :
    ∃c, right.Executes g (state t k s.val (d-s.val) p h answer [] [] (fields dt nt [] [] [] [] []))
      (state t k s.val (d-s.val) p h answer [] []
        (fields dt nt (signedBits (interpolationDenominator d s)) (signedBits (interpolationNegativeNumerator d s)) [] [] [])) c ∧
      c≤GridWeightsRuntime.pairTime.eval d := by
  obtain ⟨c,hc,hb⟩ := GridWeightsRuntime.pairProgram_executes g d s
  refine ⟨c,?_,hb⟩
  apply rename_executes_to GridWeightsRuntime.pairProgram rightEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h11 : i.val≠11 := by intro h;exact hi 2 (Fin.ext h.symm)
    have h12 : i.val≠12 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [state,fields,h11,h12,if_false]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
