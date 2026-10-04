import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationRankEmitter
import HiddenCircuits.GraphReduction.Runtime.MonotoneOrderCorrect
import HiddenCircuits.GraphReduction.Runtime.RankEmitterCount
import HiddenCircuits.GraphReduction.QueryRepresentations

/-! The literal comparison-count emitter produces the exact compressed endpoint
rank vectors used by the supplied monotone permutation-diagram input. -/
namespace HiddenCircuits.GraphReduction.Runtime.MonotonePermutationRankEmitter
open Complexity
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000

def endpoint {n : ℕ} (lower : Bool) (D : PermutationDiagram (Fin n)) : Fin n→ℕ :=
  if lower then D.lower else D.upper

lemma edge_correct {p h s : ℕ} (lower : Bool) (pairs : Fin h→CutPair p) (S T : State (2*p) p)
    (i j : Fin (monotoneGraphInput pairs S T s).1) :
    edge lower (monotoneRecords pairs S T s) i.val j.val=
      decide (endpoint lower ((monotoneEnumeration S T s).diagram (retainedMonotoneDiagram pairs S T s)) j<
        endpoint lower ((monotoneEnumeration S T s).diagram (retainedMonotoneDiagram pairs S T s)) i) := by
  simp only [edge,MonotonePermutationOrderRuntime.recordLT,MonotoneOrderRuntime.orderValue,monotoneRecords,List.getElem?_map,
    List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem j.isLt,Option.map_some,Option.getD_some]
  cases lower with
  | false => exact MonotoneOrder.upperRecordLT_correct pairs S T _ _
  | true => exact MonotoneOrder.lowerRecordLT_correct pairs S T _ _

theorem bits_correct {p h s : ℕ} (lower : Bool) (pairs : Fin h→CutPair p) (S T : State (2*p) p) :
    bits lower (monotoneRecords pairs S T s)=encodeBitList
      (List.ofFn (fun i => List.replicate (endpoint lower (monotoneMatrixDiagram pairs S T s) i) true)) := by
  unfold bits
  rw [monotoneRecords_length]
  rw [RankEmitter.bits_eq_endpointCount _ _ _ (edge_correct lower pairs S T)]
  cases lower <;> rfl

theorem upper_bits_correct {p h s : ℕ} (pairs : Fin h→CutPair p) (S T : State (2*p) p) :
    bits false (monotoneRecords pairs S T s)=encodeBitList
      (List.ofFn (fun i => List.replicate ((monotoneMatrixDiagram pairs S T s).upper i) true)) :=
  bits_correct false pairs S T
 theorem lower_bits_correct {p h s : ℕ} (pairs : Fin h→CutPair p) (S T : State (2*p) p) :
    bits true (monotoneRecords pairs S T s)=encodeBitList
      (List.ofFn (fun i => List.replicate ((monotoneMatrixDiagram pairs S T s).lower i) true)) :=
  bits_correct true pairs S T
end HiddenCircuits.GraphReduction.Runtime.MonotonePermutationRankEmitter
