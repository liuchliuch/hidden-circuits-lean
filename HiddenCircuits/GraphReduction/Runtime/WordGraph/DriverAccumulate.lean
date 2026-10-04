import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverState
import HiddenCircuits.GraphReduction.Runtime.WordGraph.AccumulatorInto

/-! Fresh reconstruction: the actual rational cell embedded into the98-port driver. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic

def accumulatorEmbedding : Fin 16 ↪ Fin 98 where
  toFun i := ![16,17,18,19,20,21,22,23,24,10,11,13,14,25,26,27] i
  inj' := by decide +kernel
noncomputable def accumulate : OracleBlock 97 := RationalAccumulator.on accumulatorEmbedding

theorem accumulate_executes (g : BitString → ℕ) (w : WordInstance) (k t h l s : ℕ)
    (a b : ℤ×ℤ) (answer : BitString) (B : ℕ)
    (ha : (signedBits a.1).length ≤ B ∧ (signedBits a.2).length ≤ B)
    (hb : (signedBits b.1).length ≤ B ∧ (signedBits b.2).length ≤ B) :
    ∃c, accumulate.Executes g (state w k t h l s a answer (signedBits b.1) (signedBits b.2))
      (state w k t h l s (RationalAccumulator.step a b) answer [] []) c ∧ c ≤ AccumulatorInto.time.eval B := by
  apply RationalAccumulator.on_executes_to accumulatorEmbedding g _ _ a b B
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h10 : i.val≠10 := by intro h;exact hi 9 (Fin.ext h.symm)
    have h11 : i.val≠11 := by intro h;exact hi 10 (Fin.ext h.symm)
    have h13 : i.val≠13 := by intro h;exact hi 11 (Fin.ext h.symm)
    have h14 : i.val≠14 := by intro h;exact hi 12 (Fin.ext h.symm)
    simp only [state,h10,h11,h13,h14,if_false]
  · exact ha
  · exact hb
lemma accumulate_queryFree : accumulate.QueryFree := RationalAccumulator.on_queryFree _
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
