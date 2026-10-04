import HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCellNorm
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 800000

lemma combine_executes (g : BitString → ℕ) (t k s l p h : ℕ) (answer nt ns dt ds factor sign : ℤ) (B : ℕ)
    (hB : RegisterMachine.Bounded B (RatioCombine.registers sign answer nt ns dt ds factor)) :
    ∃c, combine.Executes g
      (state t k s l p h (signedBits answer) [] []
        (fields (signedBits dt) (signedBits nt) (signedBits ds) (signedBits ns) (signedBits factor) (signedBits sign) (signedBits answer)))
      (state t k s l p h (signedBits answer) (signedBits (sign*answer*nt*ns)) (signedBits (dt*ds*factor))
        (fields [] [] [] [] [] [] [])) c ∧ c≤RatioCombine.time.eval B := by
  obtain ⟨c,hc,hb⟩ := RatioCombine.program_executes g sign answer nt ns dt ds factor B hB
  refine ⟨c,?_,hb⟩
  apply rename_executes_to RatioCombine.program combineEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h7 : i.val≠7 := by intro h;exact hi 0 (Fin.ext h.symm)
    have h8 : i.val≠8 := by intro h;exact hi 1 (Fin.ext h.symm)
    have h9 : i.val≠9 := by intro h;exact hi 13 (Fin.ext h.symm)
    have h10 : i.val≠10 := by intro h;exact hi 11 (Fin.ext h.symm)
    have h11 : i.val≠11 := by intro h;exact hi 14 (Fin.ext h.symm)
    have h12 : i.val≠12 := by intro h;exact hi 12 (Fin.ext h.symm)
    have h13 : i.val≠13 := by intro h;exact hi 15 (Fin.ext h.symm)
    have h14 : i.val≠14 := by intro h;exact hi 9 (Fin.ext h.symm)
    have h15 : i.val≠15 := by intro h;exact hi 10 (Fin.ext h.symm)
    simp only [state,fields,h7,h8,h9,h10,h11,h12,h13,h14,h15,if_false]
end HiddenCircuits.GraphReduction.Runtime.WordGraph.RatioCell
