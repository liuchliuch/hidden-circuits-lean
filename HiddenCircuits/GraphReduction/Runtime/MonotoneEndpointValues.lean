import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointEmit
import HiddenCircuits.Complexity.OracleMove

namespace HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
open Complexity OracleBlock
set_option maxHeartbeats 1000000

noncomputable def saveUpper : OracleBlock 69 := moveOn 4 62 65 (by decide) (by decide) (by decide)
noncomputable def saveLower : OracleBlock 69 := moveOn 4 63 65 (by decide) (by decide) (by decide)
noncomputable def values : OracleBlock 69 := seq (countProgram false true) (seq saveUpper
  (seq (countProgram true true) (seq saveLower emitPair)))
lemma saveUpper_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (u : ℕ) :
    saveUpper.Executes g (state R i k candidates ranks A (List.replicate u true))
      (state R i k candidates ranks A [] (List.replicate u true)) (6*u+5) := by
  convert moveOn_executes g (4:Fin 70) 62 65 (by decide) (by decide) (by decide)
    (state R i k candidates ranks A (List.replicate u true)) rfl using 1
  · funext j;fin_cases j <;> simp [state,combine,high,MatrixEmitter.store,MatrixEmitter.port]
  · simp [state,combine,high,MatrixEmitter.store,MatrixEmitter.port]
lemma saveLower_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (u v : ℕ) :
    saveLower.Executes g (state R i k candidates ranks A (List.replicate v true) (List.replicate u true))
      (state R i k candidates ranks A [] (List.replicate u true) (List.replicate v true)) (6*v+5) := by
  convert moveOn_executes g (4:Fin 70) 63 65 (by decide) (by decide) (by decide)
    (state R i k candidates ranks A (List.replicate v true) (List.replicate u true)) rfl using 1
  · funext j;fin_cases j <;> simp [state,combine,high,MatrixEmitter.store,MatrixEmitter.port]
  · simp [state,combine,high,MatrixEmitter.store,MatrixEmitter.port]
lemma values_executes (g : BitString→ℕ) (R : List VertexRecord) (i k : ℕ)
    (candidates ranks : BitString) (A : Accum) (hi:i<R.length) :
    ∃c,values.Executes g (state R i k candidates ranks A)
      (state R i k candidates ranks (emitValues A (countValue false true R i) (countValue true true R i))) c ∧
      c≤2*countBound R.length (encodeBitList (R.map encodeVertex)).length+44*R.length+56 := by
  obtain ⟨a,ha,hab⟩:=count_executes g false true R i k candidates ranks A [] [] hi
  have hb:=saveUpper_executes g R i k candidates ranks A (countValue false true R i)
  obtain ⟨c,hc,hcb⟩:=count_executes g true true R i k candidates ranks A (List.replicate (countValue false true R i) true) [] hi
  have hd:=saveLower_executes g R i k candidates ranks A (countValue false true R i) (countValue true true R i)
  obtain ⟨e,he,heb⟩:=emitPair_executes g R i k candidates ranks A (countValue false true R i) (countValue true true R i)
  have hu:=countValue_le false true R i
  have hv:=countValue_le true true R i
  exact ⟨_,seq_executes _ _ g ha (seq_executes _ _ g hb (seq_executes _ _ g hc (seq_executes _ _ g hd he))),by omega⟩
lemma values_queryFree : values.QueryFree := seq_queryFree _ _ (count_queryFree _ _)
  (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (count_queryFree _ _)
    (seq_queryFree _ _ (moveOn_queryFree _ _ _ _ _ _) emitPair_queryFree)))
end HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointRuntime
