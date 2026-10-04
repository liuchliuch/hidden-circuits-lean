import HiddenCircuits.DH.Runtime.BinaryPipelineStages
import HiddenCircuits.DH.Runtime.NumericRounds

/-! A single fixed finite program parses every bit string,
initializes its own state, executes its own n-round pruning scan, and computes
the final binary count. Invalid graph encodings take a total zero branch. -/
namespace HiddenCircuits.DH.Runtime.BinaryPipeline
open Complexity OracleBlock Polynomial PairCheck
open HiddenCircuits.Approximation.SamplerRuntime
set_option maxHeartbeats 1800000

noncomputable def good : OracleBlock 53 := seq (clear 0) (seq initializeStage (seq NumericRounds.program finish))
noncomputable def guard : OracleBlock 53 := branchPop 1 skip skip good
noncomputable def core : OracleBlock 53 := seq parser guard
noncomputable def coreTime : Polynomial ℕ :=
  GraphParser.time+X+NumericInitialize.time+NumericRounds.time+FinalProduct.numericTime+20

lemma good_executes (g : BitString→ℕ) {raw : BitString} {G : GraphInput}
    (h : GraphInput.decode raw=some G) :
    ∃t,good.Executes g (Function.update (parsed raw) 1 [])
      (finished (MatrixData.ofGraph G.2) (NumericStateModel.rawRun (MatrixData.ofGraph G.2) G.1 (NumericStateModel.initial G.1))) t ∧
      t≤raw.length+NumericInitialize.time.eval G.1+NumericRounds.time.eval G.1+FinalProduct.numericTime.eval G.1+7 := by
  have ha:=clearInput_executes g h
  obtain ⟨b,hb,hbb⟩:=initialize_executes g (MatrixData.ofGraph G.2)
  obtain ⟨c,hc,hcb⟩:=NumericRounds.executes g (MatrixData.ofGraph G.2) (NumericStateModel.initial G.1) (NumericStateModel.initial_safe G.1)
  obtain ⟨d,hd,hdb⟩:=finish_executes g (MatrixData.ofGraph G.2)
    (NumericStateModel.rawRun (MatrixData.ofGraph G.2) G.1 (NumericStateModel.initial G.1))
    (NumericStateModel.rawRun_safe _ _ _ (NumericStateModel.initial_safe G.1))
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc hd)),by omega⟩

/-- The total core's runtime is polynomial on all binary inputs, not only on
encodings satisfying the graph-class promise. -/
lemma core_executes (g : BitString→ℕ) (raw : BitString) :
    ∃s : Store 53,∃t,core.Executes g (input raw) s t ∧ s 2=BinaryModel.function raw ∧ t≤coreTime.eval raw.length := by
  obtain ⟨c,hc,hcb⟩:=parser_executes g raw
  cases h:GraphInput.decode raw with
  | none =>
    have hd:guard.Executes g (parsed raw) (Function.update (parsed raw) 1 []) 3:=by
      apply branchPop_false _ _ _ _ g (rest:=[]) (by simp [parsed,h])
      exact skip_executes _ _
    refine ⟨_,_,seq_executes _ _ g hc hd,?_,?_⟩
    · change []=BinaryModel.function raw
      exact (BinaryModel.malformed h).symm
    · simp only [coreTime,eval_add,eval_X,eval_ofNat];omega
  | some G =>
    obtain ⟨d,hd,hdb⟩:=good_executes g h
    have he:guard.Executes g (parsed raw)
        (finished (MatrixData.ofGraph G.2) (NumericStateModel.rawRun (MatrixData.ofGraph G.2) G.1 (NumericStateModel.initial G.1))) (d+2):=
      branchPop_true _ _ _ _ g (by simp [parsed,h]) hd
    refine ⟨_,_,seq_executes _ _ g hc he,?_,?_⟩
    · simp [finished,NumericRounds.state,BinaryModel.function,BinaryModel.count,h,BinaryModel.matrixCount]
    · have hn:=decoded_size_le h
      have hm1:=polynomial_nat_eval_mono NumericInitialize.time hn
      have hm2:=polynomial_nat_eval_mono NumericRounds.time hn
      have hm3:=polynomial_nat_eval_mono FinalProduct.numericTime hn
      dsimp only at hm1 hm2 hm3
      simp only [coreTime,eval_add,eval_X,eval_ofNat];omega

lemma good_queryFree : good.QueryFree := seq_queryFree _ _ (clear_queryFree _)
  (seq_queryFree _ _ initialize_queryFree (seq_queryFree _ _ NumericRounds.queryFree finish_queryFree))
lemma guard_queryFree : guard.QueryFree := branchPop_queryFree _ _ _ _ skip_queryFree skip_queryFree good_queryFree
lemma core_queryFree : core.QueryFree := seq_queryFree _ _ parser_queryFree guard_queryFree
end HiddenCircuits.DH.Runtime.BinaryPipeline
