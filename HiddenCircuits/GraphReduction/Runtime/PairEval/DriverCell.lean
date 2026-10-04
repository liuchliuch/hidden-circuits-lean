import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverQuery
import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphBounds
import HiddenCircuits.GraphReduction.Runtime.PairEval.DriverLoop

/-! A concrete charged oracle cell: query, integer-ratio production, rational
accumulation and physical erasure, with a closed canonical-input-bit bound. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
open Complexity OracleBlock BinaryArithmetic Polynomial WordGraph
set_option maxHeartbeats 1000000

noncomputable def cell (kind : Target) : OracleBlock 97 :=
  seq (queryCell kind) (seq (ratioCell (modelKind kind)) (seq accumulate (clear 12)))
noncomputable def cellBound (kind : Target) (g : BitString→ℕ) (w : PairInput) (s : GraphRecovery.Index w) (BC BA : ℕ) : ℕ :=
  (queryTime kind).eval ((pairInputBits w).length+s.val+(signedBits (answerValue kind g w s:ℤ)).length)+
  GraphRatio.costBound (modelKind kind) w s (answerValue kind g w s) BC+
  AccumulatorInto.time.eval BA+(signedBits (answerValue kind g w s:ℤ)).length+7

theorem cell_executes (kind : Target) (g : BitString→ℕ) (w : PairInput) (s : GraphRecovery.Index w)
    (a : ℤ×ℤ) (BC BA : ℕ) (hC : GraphRatio.componentBound (modelKind kind) w s (answerValue kind g w s) BC)
    (hA : (signedBits a.1).length≤BA ∧ (signedBits a.2).length≤BA)
    (hR : (signedBits (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s)).1).length≤BA ∧
      (signedBits (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s)).2).length≤BA) :
    ∃c,(cell kind).Executes g (state w (degree w-s.val) s.val a [] [] [])
      (state w (degree w-s.val) s.val (RationalAccumulator.step a (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s))) [] [] []) c ∧
      c ≤ cellBound kind g w s BC BA := by
  obtain ⟨c,hc,hcb⟩ := queryCell_executes kind g w s a
  obtain ⟨d,hd,hdb⟩ := ratioCell_executes g (modelKind kind) w s a (answerValue kind g w s) BC hC
  obtain ⟨e,he,heb⟩ := accumulate_executes g w (degree w-s.val) s.val a
    (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s)) (signedBits (answerValue kind g w s:ℤ)) BA hA hR
  have hz : (clear (12:Fin 98)).Executes g
      (state w (degree w-s.val) s.val (RationalAccumulator.step a (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s)))
        (signedBits (answerValue kind g w s:ℤ)) [] [])
      (state w (degree w-s.val) s.val (RationalAccumulator.step a (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s))) [] [] [])
      ((signedBits (answerValue kind g w s:ℤ)).length+1) := by
    convert clear_executes g (12:Fin 98)
      (state w (degree w-s.val) s.val (RationalAccumulator.step a (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s)))
        (signedBits (answerValue kind g w s:ℤ)) [] []) using 1
    funext i;fin_cases i <;> rfl
  exact ⟨_,seq_executes _ _ g hc (seq_executes _ _ g hd (seq_executes _ _ g he hz)),by unfold cellBound;omega⟩

noncomputable def cellTime (kind : Target) : Polynomial ℕ :=
  (queryTime kind).comp (X+GraphBounds.degreeP+GraphBounds.answerP)+
  (GraphRatio.rightTime (modelKind kind)).comp GraphBounds.degreeP+
  (GraphRatio.normTime (modelKind kind)).comp (GraphBounds.degreeP+2*X)+
  6*GraphBounds.answerP+RatioCombine.time.comp GraphBounds.componentP+
  AccumulatorInto.time.comp GraphBounds.accumulatorP+27

lemma actual_cellBound (kind : Target) (g : BitString→ℕ) (w : PairInput) (s : GraphRecovery.Index w)
    (hg : CorrectOracle kind g w) :
    cellBound kind g w s (GraphBounds.componentP.eval (pairInputBits w).length) (GraphBounds.accumulatorP.eval (pairInputBits w).length) ≤
      (cellTime kind).eval (pairInputBits w).length := by
  let L := (pairInputBits w).length
  have hp := (GraphBounds.parameter_bounds w).1
  have hh := (GraphBounds.parameter_bounds w).2.1
  have hd := (GraphBounds.parameter_bounds w).2.2
  have hs := GraphBounds.index_bound w s
  change w.particles ≤ L at hp
  change w.pairs.length ≤ L at hh
  change GraphRecovery.degree w ≤ GraphBounds.degreeP.eval L at hd
  change s.val ≤ GraphBounds.degreeP.eval L at hs
  have ha : (signedBits (answerValue kind g w s:ℤ)).length≤GraphBounds.answerP.eval L := by rw [hg s];exact GraphBounds.query_answer_length _ _ _
  have hq := polynomial_nat_eval_mono (queryTime kind)
    (show L+s.val+(signedBits (answerValue kind g w s:ℤ)).length ≤ L+GraphBounds.degreeP.eval L+GraphBounds.answerP.eval L by omega)
  have hr := polynomial_nat_eval_mono (GraphRatio.rightTime (modelKind kind)) hd
  have hn := polynomial_nat_eval_mono (GraphRatio.normTime (modelKind kind))
    (show s.val+w.pairs.length+w.particles ≤ GraphBounds.degreeP.eval L+2*L by omega)
  dsimp only at hq hr hn
  simp only [cellTime,eval_add,eval_comp,eval_X,eval_mul,eval_ofNat]
  unfold cellBound GraphRatio.costBound
  change (queryTime kind).eval (L+s.val+(signedBits (answerValue kind g w s:ℤ)).length)+
    ((GraphRatio.rightTime (modelKind kind)).eval (GraphRecovery.degree w)+(GraphRatio.normTime (modelKind kind)).eval (s.val+w.pairs.length+w.particles)+
      5*(signedBits (answerValue kind g w s:ℤ)).length+RatioCombine.time.eval (GraphBounds.componentP.eval L)+20)+
    AccumulatorInto.time.eval (GraphBounds.accumulatorP.eval L)+(signedBits (answerValue kind g w s:ℤ)).length+7 ≤ _
  dsimp [L] at *
  omega

lemma cell_spec (kind : Target) (g : BitString→ℕ) (w : PairInput) (hg : CorrectOracle kind g w) :
    CellSpec (cell kind) (modelKind kind) g w (GraphBounds.accumulatorP.eval (pairInputBits w).length) ((cellTime kind).eval (pairInputBits w).length) := by
  intro s a ha ht
  have hc : GraphRatio.componentBound (modelKind kind) w s (answerValue kind g w s)
      (GraphBounds.componentP.eval (pairInputBits w).length) := by
    rw [hg s]
    exact GraphBounds.registers_bounded (modelKind kind) w s
  have hr : (signedBits (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s)).1).length≤GraphBounds.accumulatorP.eval (pairInputBits w).length ∧
      (signedBits (GraphRecovery.ratio (modelKind kind) w s (answerValue kind g w s)).2).length≤GraphBounds.accumulatorP.eval (pairInputBits w).length := by
    rw [hg s]
    exact ht
  obtain ⟨c,h,hb⟩ := cell_executes kind g w s a _ _ hc ha hr
  rw [hg s] at h
  exact ⟨c,h,hb.trans (actual_cellBound kind g w s hg)⟩
end HiddenCircuits.GraphReduction.Runtime.PairEval.Driver
