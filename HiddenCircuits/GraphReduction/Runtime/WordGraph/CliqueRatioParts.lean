import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCellParts
import HiddenCircuits.Complexity.EvenWeightsRuntime
import HiddenCircuits.GraphReduction.Runtime.WordGraph.OddFactorialNormalization

/-! Fresh reconstructed clique arithmetic cell frames sharing the verified
ordinary driver layout and five-product combination kernel. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRatioCell
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 1000000
abbrev state := RatioCell.state
abbrev fields := RatioCell.fields
noncomputable abbrev left := RatioCell.left
noncomputable abbrev combine := RatioCell.combine
noncomputable abbrev copyAnswer := RatioCell.copyAnswer
abbrev left_executes := RatioCell.left_executes
abbrev copyAnswer_executes := RatioCell.copyAnswer_executes
abbrev combine_executes := RatioCell.combine_executes

def rightEmbedding : Fin 31 ↪ Fin 53 where
  toFun i := if i.val=0 then 2 else if i.val=1 then 3 else if i.val=2 then 11 else if i.val=3 then 12
    else ⟨i.val+12,by omega⟩
  inj' := by decide +kernel
noncomputable def right : OracleBlock 52 := rename EvenWeightsRuntime.program rightEmbedding
noncomputable def norm (mode : Bool) : OracleBlock 52 := rename (OddFactorialNormalization.program mode) RatioCell.normEmbedding

lemma right_executes (g : BitString → ℕ) (d : ℕ) (s : Fin (d+1)) (t k p h : ℕ)
    (answer dt nt : BitString) :
    ∃c, right.Executes g (state t k s.val (d-s.val) p h answer [] [] (fields dt nt [] [] [] [] []))
      (state t k s.val (d-s.val) p h answer [] []
        (fields dt nt (signedBits (EvenWeights.denominator d s)) (signedBits (EvenWeights.numerator d s)) [] [] [])) c ∧
      c ≤ EvenWeightsRuntime.time.eval d := by
  obtain ⟨c,hc,hb⟩ := EvenWeightsRuntime.program_executes g d s
  refine ⟨c,?_,hb⟩
  apply rename_executes_to EvenWeightsRuntime.program rightEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h11 : i.val≠11 := by intro h;exact hi 2 (Fin.ext h.symm)
    have h12 : i.val≠12 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [state,fields,RatioCell.state,RatioCell.fields,h11,h12,if_false]

lemma norm_executes (g : BitString → ℕ) (mode : Bool) (t k s l p h : ℕ) (answer dt nt ds ns : BitString) :
    ∃c, (norm mode).Executes g (state t k s l p h answer [] [] (fields dt nt ds ns [] [] []))
      (state t k s l p h answer [] []
        (fields dt nt ds ns (signedBits ((oddFactorial s:ℤ)^(OddFactorialNormalization.exponent mode h)))
          (signedBits (OddFactorialNormalization.signValue mode h p)) [])) c ∧
      c ≤ OddFactorialNormalization.time.eval (s+h+p) := by
  obtain ⟨c,hc,hb⟩ := OddFactorialNormalization.program_executes g mode s h p
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (OddFactorialNormalization.program mode) RatioCell.normEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h13 : i.val≠13 := by intro h;exact hi 3 (Fin.ext h.symm)
    have h14 : i.val≠14 := by intro h;exact hi 4 (Fin.ext h.symm)
    simp only [state,fields,RatioCell.state,RatioCell.fields,h13,h14,if_false]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRatioCell
