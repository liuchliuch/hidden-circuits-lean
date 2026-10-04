import HiddenCircuits.GraphReduction.Runtime.CliqueCallback
import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptorCorrect
import HiddenCircuits.GraphReduction.Runtime.MonotoneEmitter

namespace HiddenCircuits.GraphReduction.Runtime.CliqueEmitter
open Complexity OracleBlock Polynomial
set_option maxHeartbeats 700000

def graphInput {p h : ℕ} (mode : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : GraphInput :=
  if mode then privateGraphInput pairs S T s else unitGraphInput pairs S T s
def records {p h : ℕ} (mode : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : List VertexRecord :=
  if mode then privateRecords pairs S T s else unitRecords pairs S T s
def descriptor {p h : ℕ} (mode : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) : BitString :=
  encodeBitList ((records mode pairs S T s).map encodeVertex)
@[simp] lemma records_length {p h : ℕ} (mode : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (records mode pairs S T s).length=(graphInput mode pairs S T s).1 := by
  cases mode <;> simp [records,graphInput,unitRecords_length,privateRecords_length]

lemma recordEdge_correct {p h : ℕ} (mode : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ)
    (i j : Fin (graphInput mode pairs S T s).1) :
    CliqueCallback.recordEdge mode (records mode pairs S T s) i.val j.val=(graphInput mode pairs S T s).2.edge i j := by
  cases mode
  · have hi:i.val<(unitEnumeration S T s).labels.length := i.isLt
    have hj:j.val<(unitEnumeration S T s).labels.length := j.isLt
    simp only [records,Bool.false_eq_true,ite_false,CliqueCallback.recordEdge,unitRecords,List.getElem?_map,
      List.getElem?_eq_getElem,hi,hj,Option.map_some,Option.getD_some]
    exact unitRecordAdj_correct pairs S T _ _
  · have hi:i.val<(privateEnumeration S T s).labels.length := i.isLt
    have hj:j.val<(privateEnumeration S T s).labels.length := j.isLt
    simp only [records,ite_true,CliqueCallback.recordEdge,privateRecords,List.getElem?_map,
      List.getElem?_eq_getElem,hi,hj,Option.map_some,Option.getD_some]
    exact privateRecordAdj_correct pairs S T _ _

noncomputable def program (mode : Bool) : OracleBlock 56 := MatrixEmitter.block (CliqueCallback.program mode)
noncomputable def time : Polynomial ℕ := 10000*(X+1)^4

lemma cost_bound (n L : ℕ) : n*n*(CliqueCallback.bound n L+18)+40*n+30≤time.eval (n+L) := by
  let M:=n+L
  have hn:n≤M:=by dsimp[M];omega
  have hL:L≤M:=by dsimp[M];omega
  calc
    _≤M*M*(CliqueCallback.bound M M+18)+40*M+30 := by unfold CliqueCallback.bound lookupBound;gcongr
    _≤_ := by
      change _≤time.eval M
      simp only [time,eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
      unfold CliqueCallback.bound lookupBound
      ring_nf
      omega

theorem program_polynomial {p h : ℕ} (g : BitString → ℕ) (mode : Bool) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    ∃c,(program mode).Executes g
      (MatrixEmitter.store (k:=49) (graphInput mode pairs S T s).1 0 0 [] [] [] [] (callbackParams (descriptor mode pairs S T s)))
      (Function.update (MatrixEmitter.store (k:=49) (graphInput mode pairs S T s).1 0 0 [] [] [] [] (callbackParams (descriptor mode pairs S T s)))
        (MatrixEmitter.port 7) (graphInput mode pairs S T s).encode) c ∧
      c≤time.eval ((graphInput mode pairs S T s).1+(descriptor mode pairs S T s).length) := by
  obtain ⟨c,hc,hb⟩ := MatrixEmitter.graph_executes (graphInput mode pairs S T s).2 (CliqueCallback.program mode)
    (CliqueCallback.recordEdge mode (records mode pairs S T s)) (recordEdge_correct mode pairs S T s)
    (CliqueCallback.bound (graphInput mode pairs S T s).1 (descriptor mode pairs S T s).length)
    (callbackParams (descriptor mode pairs S T s)) (by
      intro g i j out inner outer hi hj
      have hn := records_length mode pairs S T s
      have hi':i<(records mode pairs S T s).length:=by omega
      have hj':j<(records mode pairs S T s).length:=by omega
      simpa only [hn,descriptor] using CliqueCallback.framed g mode (records mode pairs S T s) i j hi' hj' out inner outer) g
  exact ⟨c,hc,hb.trans (cost_bound _ _)⟩
lemma program_queryFree (mode : Bool) : (program mode).QueryFree := MatrixEmitter.block_queryFree _ (CliqueCallback.program_queryFree _)
end HiddenCircuits.GraphReduction.Runtime.CliqueEmitter

namespace HiddenCircuits.GraphReduction.Runtime
noncomputable def unitEmitter : Complexity.OracleBlock 56 := CliqueEmitter.program false
noncomputable def privateEmitter : Complexity.OracleBlock 56 := CliqueEmitter.program true
end HiddenCircuits.GraphReduction.Runtime
