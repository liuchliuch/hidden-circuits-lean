import HiddenCircuits.GraphReduction.Runtime.WordGraph.WideSolver
import HiddenCircuits.GraphReduction.Runtime.WordGraph.DriverPolynomial

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriver
open Complexity OracleBlock BinaryArithmetic Polynomial
set_option maxHeartbeats 600000

def queryStore (bits : BitString) (t s : ℕ) (answer : BitString) : Store 123 := fun q =>
  if q.val=0 then bits else if q.val=1 then List.replicate t true else if q.val=2 then List.replicate s true
  else if q.val=3 then answer else []

def queryEmbedding : Fin 124 ↪ Fin 136 where
  toFun i := ⟨Driver.queryPort i.val,by unfold Driver.queryPort;split_ifs <;> have := i.isLt <;> omega⟩
  inj' := by intro i j h;apply Fin.ext;exact Driver.queryPort_injective (congrArg Fin.val h)

/-- Operational contract of the actual native-input query block. The third
input is the ordinary interpolation index; endpoint data are physically emitted. -/
def QuerySpec (Q : OracleBlock 123) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString) (P : Polynomial ℕ) : Prop :=
  ∀w t s, ∃c, Q.Executes g (queryStore (wordBits w) t s [])
    (queryStore (wordBits w) t s (signedBits (g (bytes w t s):ℤ))) c ∧
    c≤P.eval ((wordBits w).length+t+s+(signedBits (g (bytes w t s):ℤ)).length)

noncomputable def queryCell (Q : OracleBlock 123) : OracleBlock 135 := rename Q queryEmbedding
noncomputable def ratioCell : OracleBlock 135 := WideDriver.lift 38 Driver.ratioCell
noncomputable def cell (Q : OracleBlock 123) : OracleBlock 135 :=
  seq (queryCell Q) (seq ratioCell (seq (WideDriver.lift 38 Driver.accumulate) (WideDriver.lift 38 (clear 12))))

def answerValue (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString) (w : WordInstance) (q : Recovery.Index w) : ℕ :=
  g (bytes w q.1.val q.2.val)
def CorrectOracle (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString) (w : WordInstance) : Prop :=
  ∀q,answerValue g bytes w q=perfectMatchingCount (Recovery.query w q).2.graph

lemma queryCell_executes (Q : OracleBlock 123) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (P : Polynomial ℕ) (hQ : QuerySpec Q g bytes P) (w : WordInstance) (q : Recovery.Index w) (a : ℤ×ℤ) :
    ∃c, (queryCell Q).Executes g
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answerValue g bytes w q:ℤ)) [] []) c ∧
      c≤P.eval ((wordBits w).length+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length) := by
  obtain ⟨c,hc,hb⟩ := hQ w q.1.val q.2.val
  refine ⟨c,?_,hb⟩
  apply rename_executes_to Q queryEmbedding g hc
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i <;> rfl
  · intro i hi
    have h12 : i.val≠12 := by intro h;exact hi 3 (Fin.ext h.symm)
    simp only [WideDriver.state,WideDriver.extend,Driver.state,h12,if_false]

lemma ratioCell_executes (g : BitString → ℕ) (w : WordInstance) (q : Recovery.Index w)
    (a : ℤ×ℤ) (answer B : ℕ) (hB : RatioCell.componentBound w q answer B) :
    ∃c, ratioCell.Executes g
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answer:ℤ)) [] [])
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a
        (signedBits (answer:ℤ)) (signedBits (Recovery.ratio w q answer).1) (signedBits (Recovery.ratio w q answer).2)) c ∧
      c ≤ RatioCell.costBound w q answer B := by
  obtain ⟨c,hc,hb⟩ := Driver.ratioCell_executes g w q a answer B hB
  exact ⟨c,WideDriver.lift_executes 38 Driver.ratioCell g _ _ _ hc,hb⟩

noncomputable def cellBound (P : Polynomial ℕ) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (w : WordInstance) (q : Recovery.Index w) (BC BA : ℕ) : ℕ :=
  P.eval ((wordBits w).length+q.1.val+q.2.val+(signedBits (answerValue g bytes w q:ℤ)).length)+
  RatioCell.costBound w q (answerValue g bytes w q) BC+AccumulatorInto.time.eval BA+
  (signedBits (answerValue g bytes w q:ℤ)).length+7

theorem cell_executes (Q : OracleBlock 123) (g : BitString → ℕ) (bytes : WordInstance → ℕ → ℕ → BitString)
    (P : Polynomial ℕ) (hQ : QuerySpec Q g bytes P) (w : WordInstance) (q : Recovery.Index w)
    (a : ℤ×ℤ) (BC BA : ℕ) (hC : RatioCell.componentBound w q (answerValue g bytes w q) BC)
    (hA : (signedBits a.1).length≤BA ∧ (signedBits a.2).length≤BA)
    (hR : (signedBits (Recovery.ratio w q (answerValue g bytes w q)).1).length≤BA ∧
      (signedBits (Recovery.ratio w q (answerValue g bytes w q)).2).length≤BA) :
    ∃c, (cell Q).Executes g
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val a [] [] [])
      (WideDriver.state 38 w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g bytes w q))) [] [] []) c ∧
      c≤cellBound P g bytes w q BC BA := by
  obtain ⟨c,hc,hcb⟩ := queryCell_executes Q g bytes P hQ w q a
  obtain ⟨d,hd,hdb⟩ := ratioCell_executes g w q a (answerValue g bytes w q) BC hC
  obtain ⟨e,he,heb⟩ := Driver.accumulate_executes g w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1)
    (Recovery.innerDegree w q.1-q.2.val) q.2.val a (Recovery.ratio w q (answerValue g bytes w q))
    (signedBits (answerValue g bytes w q:ℤ)) BA hA hR
  have hz : (clear (12:Fin 98)).Executes g
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g bytes w q))) (signedBits (answerValue g bytes w q:ℤ)) [] [])
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g bytes w q))) [] [] [])
      ((signedBits (answerValue g bytes w q:ℤ)).length+1) := by
    convert clear_executes g (12:Fin 98)
      (Driver.state w (Recovery.degree w-q.1.val) q.1.val (Recovery.height w q.1) (Recovery.innerDegree w q.1-q.2.val) q.2.val
        (RationalAccumulator.step a (Recovery.ratio w q (answerValue g bytes w q))) (signedBits (answerValue g bytes w q:ℤ)) [] []) using 1
    clear hc hd he hcb hdb heb
    funext i;fin_cases i <;> rfl
  have heW := WideDriver.lift_executes 38 Driver.accumulate g _ _ _ he
  have hzW := WideDriver.lift_executes 38 (clear (12:Fin 98)) g _ _ _ hz
  exact ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hd (seq_executes _ _ g heW hzW)),by unfold cellBound;omega⟩
end HiddenCircuits.GraphReduction.Runtime.WordGraph.EndpointDriver
