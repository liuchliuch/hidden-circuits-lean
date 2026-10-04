import HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriverPolynomial

/-! Fresh ordinary-interpolation composition for a concrete native endpoint query
block. The final endpoint solver discharges every operational query contract. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
open Driver (accumulatorP componentP accumulatorP_eval componentP_eval)
set_option maxHeartbeats 700000

noncomputable def term (w : WordInstance) (q : Recovery.Index w) : ℤ×ℤ :=
  Recovery.ratio w q (perfectMatchingCount (Recovery.query w q).2.graph)

lemma initialBitBound (w : WordInstance) (hw : w.word≠[]) :
    RationalAccumulator.BitBound (accumulatorP.eval (wordBits w).length) (0,1)
      (GenericDriver.terms w (term w)) := by
  have h := RationalAccumulator.bitBound_of_abs (0,1) (GenericDriver.terms w (term w)) 1
    (Recovery.termExponent (wordBits w).length) (by constructor <;> decide) (by
      intro b hb
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
      exact Recovery.ratio_bound w hw q)
  apply h.mono
  rw [accumulatorP_eval]
  have hl : (GenericDriver.terms w (term w)).length≤Recovery.queryCountBound (wordBits w).length := by
    simpa only [GenericDriver.terms,Recovery.terms,List.length_map] using Recovery.terms_length_bound w
  nlinarith

lemma modelSpec (Q : OracleBlock 123) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (P : Polynomial ℕ) (hQ : QuerySpec Q g bytes P) (w : WordInstance)
    (hw : w.word≠[]) (hg : CorrectOracle g bytes w) :
    WideDriver.ModelSpec (cell Q) g w (term w) accumulatorP (cellTime P) := by
  refine ⟨?_,initialBitBound w hw,?_,Recovery.terms_value w hw⟩
  · intro q a hA hR
    have hC : RatioCell.componentBound w q (answerValue g bytes w q)
        (componentP.eval (wordBits w).length) := by
      unfold RatioCell.componentBound
      rw [hg q,componentP_eval]
      exact Recovery.ratio_registers_bounded w hw q
    have hR' : (signedBits (Recovery.ratio w q (answerValue g bytes w q)).1).length≤accumulatorP.eval (wordBits w).length ∧
        (signedBits (Recovery.ratio w q (answerValue g bytes w q)).2).length≤accumulatorP.eval (wordBits w).length := by
      rw [hg q]
      exact hR
    obtain ⟨c,hc,hb⟩ := cell_executes Q g bytes P hQ w q a
      (componentP.eval (wordBits w).length) (accumulatorP.eval (wordBits w).length) hC hA hR'
    rw [hg q] at hc
    exact ⟨c,hc,hb.trans (actual_cellBound P g bytes w hw q (hg q))⟩
  · intro q
    exact Recovery.ratio_nonzero _ _ _

noncomputable def program (Q : OracleBlock 123) : OracleBlock 135 := WideDriver.program (cell Q)
noncomputable def time (P : Polynomial ℕ) : Polynomial ℕ := GenericDriver.time accumulatorP (cellTime P)

theorem program_executes (Q : OracleBlock 123) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (P : Polynomial ℕ) (hQ : QuerySpec Q g bytes P) (w : WordInstance)
    (hg : w.word≠[] → CorrectOracle g bytes w) :
    ∃z : ℤ, ∃c, (program Q).Executes g (Function.update (fun _ => []) 0 (wordBits w))
      (Function.update (fun _ => []) 0 (signedBits z)) c ∧ w.value=(z:ℚ) ∧ c ≤ (time P).eval (wordBits w).length := by
  apply WideDriver.program_executes (cell Q) g w (term w) accumulatorP (cellTime P)
  intro hw
  exact modelSpec Q g bytes P hQ w hw (hg hw)
end HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriver
