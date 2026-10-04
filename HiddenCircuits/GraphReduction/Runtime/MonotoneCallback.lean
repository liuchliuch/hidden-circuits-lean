import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackLookup
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackParse
import HiddenCircuits.GraphReduction.Runtime.MonotoneCallbackEdges

/-! The fixed actual structural-query adjacency callback. -/
namespace HiddenCircuits.GraphReduction.Runtime
open Complexity Complexity.OracleBlock

theorem monotoneCallback_executes (g : BitString → ℕ) (records : List VertexRecord)
    (i j : Fin records.length) (out inner outer : BitString) :
    ∃ t, monotoneCallback.Executes g
      (callbackStore (queryContext records i.val j.val out inner outer) [] [] [] (fun _ => []) (fun _ => []) [] [])
      (callbackStore (queryContext records i.val j.val out inner outer) [recordEdge records i.val j.val]
        [] [] (fun _ => []) (fun _ => []) [] []) t ∧
      t≤callbackBound records.length (encodeBitList (records.map encodeVertex)).length := by
  let c := queryContext records i.val j.val out inner outer
  let x := records.get i
  let y := records.get j
  obtain ⟨a,ha,hba⟩ := callbackLookup_executes g records i j out inner outer
  have hp := callbackParse_executes g c x y
  obtain ⟨b,hb,hbb⟩ := callbackEdges_executes g c x y
  obtain ⟨t,ht,htb⟩ := callbackCleanup_executes g c x y
  have hedge : recordEdge records i.val j.val=recordAdj x y := by
    simp [recordEdge,x,y,List.getElem?_eq_getElem,i.isLt,j.isLt]
  refine ⟨a+(((5*x.layer+5*x.track+2*x.cut.index+49)+(5*y.layer+5*y.track+2*y.cut.index+49)+2)+(b+t+2)+2)+2,?_,?_⟩
  · rw [hedge]
    exact seq_executes _ _ g ha (seq_executes _ _ g hp (seq_executes _ _ g hb ht))
  · have hx := descriptor_record_length records i
    have hy := descriptor_record_length records j
    have hxp := recordParse_cost_le x
    have hyp := recordParse_cost_le y
    unfold callbackBound
    unfold dirSize at hbb htb
    change (encodeVertex x).length≤_ at hx
    change (encodeVertex y).length≤_ at hy
    omega

lemma monotoneCallback_queryFree : monotoneCallback.QueryFree :=
  seq_queryFree _ _ callbackLookup_queryFree (seq_queryFree _ _ callbackParse_queryFree
    (seq_queryFree _ _ callbackEdges_queryFree (clearList_queryFree _)))

/-- The callback writes precisely its one reserved bit and preserves the current
matrix stream, both clocks, descriptor, and all other parameters. -/
theorem monotoneCallback_framed (g : BitString → ℕ) (records : List VertexRecord) (i j : ℕ)
    (hi : i<records.length) (hj : j<records.length) (out inner outer : BitString) :
    ∃ t, monotoneCallback.Executes g
      (MatrixEmitter.store (k := 49) records.length i j [] out inner outer (callbackParams (encodeBitList (records.map encodeVertex))))
      (MatrixEmitter.store (k := 49) records.length i j [recordEdge records i j] out inner outer
        (callbackParams (encodeBitList (records.map encodeVertex)))) t ∧
      t≤callbackBound records.length (encodeBitList (records.map encodeVertex)).length := by
  simpa only [callbackStore_initial,queryContext] using monotoneCallback_executes g records ⟨i,hi⟩ ⟨j,hj⟩ out inner outer

end HiddenCircuits.GraphReduction.Runtime
