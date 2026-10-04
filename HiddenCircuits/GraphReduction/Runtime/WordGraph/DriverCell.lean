import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverPorts
import HiddenCircuits.GraphReduction.Runtime.WordGraph.QueryAnswer

/-! Fresh reconstructed driver cell: one encoded graph query, ratio generation,
integer rational accumulation, and answer erasure on the physical store. -/
namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 900000

noncomputable def queryCell : OracleBlock 97 := rename QueryAnswer.program queryEmbedding
noncomputable def cell : OracleBlock 97 := seq queryCell (seq ratioCell (seq accumulate (clear 12)))
def answerValue (g : BitString → ℕ) (w : WordInstance) (q : Recovery.Index w) : ℕ :=
  g (Recovery.query w q).encode

lemma queryCell_executes (g : BitString → ℕ) (w : WordInstance) (q : Recovery.Index w) (a : ℤ×ℤ) :
    ∃c, queryCell.Executes g
      (state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answerValue g w q:ℤ)) [] []) c ∧
      c≤QueryAnswer.time.eval ((wordBits w).length+q.1.val+q.2.val+(signedBits (answerValue g w q:ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := QueryAnswer.program_polynomial g w q.1.val q.2.val
  refine ⟨c,?_,hb⟩
  apply rename_executes_to QueryAnswer.program queryEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h12 : i.val≠12 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [state,h12,if_false]

noncomputable def cellBound (g : BitString → ℕ)
    (w : WordInstance) (q : Recovery.Index w) (BC BA : ℕ) : ℕ :=
  QueryAnswer.time.eval ((wordBits w).length+q.1.val+q.2.val+(signedBits (answerValue g w q:ℤ)).length)+
  RatioCell.costBound w q (answerValue g w q) BC+AccumulatorInto.time.eval BA+
  (signedBits (answerValue g w q:ℤ)).length+7

theorem cell_executes (g : BitString → ℕ) (w : WordInstance) (q : Recovery.Index w)
    (a : ℤ×ℤ) (BC BA : ℕ) (hC : RatioCell.componentBound w q (answerValue g w q) BC)
    (hA : (signedBits a.1).length≤BA ∧ (signedBits a.2).length≤BA)
    (hR : (signedBits (Recovery.ratio w q (answerValue g w q)).1).length≤BA ∧
      (signedBits (Recovery.ratio w q (answerValue g w q)).2).length≤BA) :
    ∃c, cell.Executes g
      (state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g w q))) [] [] []) c ∧
      c≤cellBound g w q BC BA := by
  obtain ⟨c,hc,hcb⟩ := queryCell_executes g w q a
  obtain ⟨d,hd,hdb⟩ := ratioCell_executes g w q a (answerValue g w q) BC hC
  obtain ⟨e,he,heb⟩ := accumulate_executes g w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1)
    (Recovery.innerDegree w q.1-q.2.val) q.2.val a (Recovery.ratio w q (answerValue g w q))
    (signedBits (answerValue g w q:ℤ)) BA hA hR
  have hz : (clear (12:Fin 98)).Executes g
      (state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g w q))) (signedBits (answerValue g w q:ℤ)) [] [])
      (state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g w q))) [] [] [])
      ((signedBits (answerValue g w q:ℤ)).length+1) := by
    convert clear_executes g (12:Fin 98)
      (state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g w q))) (signedBits (answerValue g w q:ℤ)) [] []) using 1
    clear hc hd he hcb hdb heb
    funext i;fin_cases i <;> rfl
  exact ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hd (seq_executes _ _ g he hz)),by unfold cellBound;omega⟩
end HiddenCircuits.GraphReduction.Runtime.WordGraph.Driver
