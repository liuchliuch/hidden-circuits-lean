import HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueRatioCell
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverCell
import HiddenCircuits.GraphReduction.Runtime.WordGraph.GenericSolver

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 600000

/-- Operational contract of the actual native-input query block. The third
input is the interpolation index; the query block physically creates 2*s probes. -/
def QuerySpec (Q : OracleBlock 85) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString) (P : Polynomial ℕ) : Prop :=
  ∀w t s, ∃c, Q.Executes g (QueryAnswer.store (wordBits w) t s [])
    (QueryAnswer.store (wordBits w) t s (signedBits (g (bytes w t s):ℤ))) c ∧
    c≤P.eval ((wordBits w).length+t+s+(signedBits (g (bytes w t s):ℤ)).length)

def ratioEmbedding : Fin 53 ↪ Fin 98 where
  toFun i := ⟨Driver.ratioPort i.val,by
    by_cases hi:i.val<9
    · exact (Driver.ratioPort_low hi).trans (by decide)
    · rw [Driver.ratioPort_high (by omega)]
      have := i.isLt;omega⟩
  inj' := by intro i j h;apply Fin.ext;exact Driver.ratioPort_injective (congrArg Fin.val h)
noncomputable def queryCell (Q : OracleBlock 85) : OracleBlock 97 := rename Q Driver.queryEmbedding
noncomputable def ratioCell (mode : Bool) : OracleBlock 97 := rename (CliqueRatioCell.program mode) ratioEmbedding
noncomputable def cell (Q : OracleBlock 85) (mode : Bool) : OracleBlock 97 :=
  seq (queryCell Q) (seq (ratioCell mode) (seq Driver.accumulate (clear 12)))

def answerValue (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString) (w : WordInstance) (q : Recovery.Index w) : ℕ :=
  g (bytes w q.1.val q.2.val)
def CorrectOracle (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString) (mode : Bool) (w : WordInstance) : Prop :=
  ∀q,answerValue g bytes w q=perfectMatchingCount (CliqueRecovery.query mode w q).2.graph

lemma queryCell_executes (Q : OracleBlock 85) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (P : Polynomial ℕ) (hQ : QuerySpec Q g bytes P) (w : WordInstance) (q : Recovery.Index w) (a : ℤ×ℤ) :
    ∃c, (queryCell Q).Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answerValue g bytes w q:ℤ)) [] []) c ∧
      c≤P.eval ((wordBits w).length+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := hQ w q.1.val q.2.val
  refine ⟨c,?_,hb⟩
  apply rename_executes_to Q Driver.queryEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h12 : i.val≠12 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [Driver.state,h12,if_false]

lemma ratioCell_executes (g : BitString → ℕ) (mode : Bool) (w : WordInstance) (q : Recovery.Index w)
    (a : ℤ×ℤ) (answer B : ℕ) (hB : CliqueRatioCell.componentBound mode w q answer B) :
    ∃c, (ratioCell mode).Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answer:ℤ)) [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answer:ℤ)) (signedBits (CliqueRecovery.ratio mode w q answer).1) (signedBits (CliqueRecovery.ratio mode w q answer).2)) c ∧
      c≤CliqueRatioCell.costBound w q answer B := by
  obtain ⟨c,hc,hb⟩ := CliqueRatioCell.program_executes g mode w q answer B hB
  refine ⟨c,?_,hb⟩
  apply rename_executes_to (CliqueRatioCell.program mode) ratioEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h13 : i.val≠13 := by intro h;exact hi 7 (Fin.ext h.symm)
    have h14 : i.val≠14 := by intro h;exact hi 8 (Fin.ext h.symm)
    simp only [Driver.state,h13,h14,if_false]

noncomputable def cellBound (P : Polynomial ℕ) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (w : WordInstance) (q : Recovery.Index w) (BC BA : ℕ) : ℕ :=
  P.eval ((wordBits w).length+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length)+
  CliqueRatioCell.costBound w q (answerValue g bytes w q) BC+AccumulatorInto.time.eval BA+
  (signedBits (answerValue g bytes w q:ℤ)).length+7

theorem cell_executes (Q : OracleBlock 85) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (P : Polynomial ℕ) (hQ : QuerySpec Q g bytes P) (mode : Bool) (w : WordInstance) (q : Recovery.Index w)
    (a : ℤ×ℤ) (BC BA : ℕ) (hC : CliqueRatioCell.componentBound mode w q (answerValue g bytes w q) BC)
    (hA : (signedBits a.1).length≤BA ∧ (signedBits a.2).length≤BA)
    (hR : (signedBits (CliqueRecovery.ratio mode w q (answerValue g bytes w q)).1).length≤BA ∧
      (signedBits (CliqueRecovery.ratio mode w q (answerValue g bytes w q)).2).length≤BA) :
    ∃c, (cell Q mode).Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio mode w q (answerValue g bytes w q))) [] [] []) c ∧
      c≤cellBound P g bytes w q BC BA := by
  obtain ⟨c,hc,hcb⟩ := queryCell_executes Q g bytes P hQ w q a
  obtain ⟨d,hd,hdb⟩ := ratioCell_executes g mode w q a (answerValue g bytes w q) BC hC
  obtain ⟨e,he,heb⟩ := Driver.accumulate_executes g w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1)
    (Recovery.innerDegree w q.1-q.2.val) q.2.val a (CliqueRecovery.ratio mode w q (answerValue g bytes w q))
    (signedBits (answerValue g bytes w q:ℤ)) BA hA hR
  have hz : (clear (12:Fin 98)).Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio mode w q (answerValue g bytes w q))) (signedBits (answerValue g bytes w q:ℤ)) [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio mode w q (answerValue g bytes w q))) [] [] [])
      ((signedBits (answerValue g bytes w q:ℤ)).length+1) := by
    convert clear_executes g (12:Fin 98)
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (CliqueRecovery.ratio mode w q (answerValue g bytes w q))) (signedBits (answerValue g bytes w q:ℤ)) [] []) using 1
    clear hc hd he hcb hdb heb
    funext i;fin_cases i <;> rfl
  exact ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hd (seq_executes _ _ g he hz)),by unfold cellBound;omega⟩
end HiddenCircuits.GraphReduction.Runtime.WordGraph.CliqueDriver
