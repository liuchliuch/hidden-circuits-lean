import HiddenCircuits.GraphReduction.Runtime.PrivateIntervalDefs
import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptorCorrect
import HiddenCircuits.GraphReduction.Runtime.RankEmitterCount

/-! The structural record predicates compute the exact two interval vectors. -/
namespace HiddenCircuits.GraphReduction.Runtime.PrivateInterval
open Complexity PrivateProbe
set_option maxHeartbeats 1200000

lemma recordLT_correct {p h s : ℕ} (pairs : Fin h → CutPair p)
    (x y : PrivateProbe.Vertex (2*p) h s) :
    recordLT (PrivateOrder.rawRecord pairs x) (PrivateOrder.rawRecord pairs y)=
      decide (intervalKey x < intervalKey y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [intervalKey_lt_iff]
  rcases x with (⟨j,u⟩|⟨j,u⟩)|⟨j|j,u⟩ <;>
    rcases y with (⟨k,v⟩|⟨k,v⟩)|⟨k|k,v⟩
  all_goals simp only [recordLT,localLT,PrivateOrder.rawRecord,intervalLayer,intervalRank,
    layerIndex,layerNumber,eliminationRank,Bool.false_eq_true,Bool.true_eq_false,
    Bool.not_false,Bool.not_true,Bool.and_false,Bool.false_and,Bool.and_true,Bool.true_and,
    Bool.or_false,Bool.false_or,Bool.or_true,Bool.true_or,beq_self_eq_true,
    (show (false==true)=false from rfl),(show (true==false)=false from rfl),
    ite_true,ite_false,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  all_goals have hu := u.isLt
  all_goals have hv := v.isLt
  all_goals omega

lemma retained_recordLT_correct {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : PrivateQueryVertex p h s S T) :
    recordLT (privateVertexRecord pairs x) (privateVertexRecord pairs y)=
      decide (intervalKey (retainedEmbedding S T s x) < intervalKey (retainedEmbedding S T s y)) := by
  rw [←PrivateOrder.rawRecord_retained pairs S T x,←PrivateOrder.rawRecord_retained pairs S T y]
  exact recordLT_correct pairs _ _

lemma endpointEdge_correct {p h s : ℕ} (left : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (i j : Fin (privateGraphInput pairs S T s).1) :
    endpointEdge left (privateRecords pairs S T s) i.val j.val =
      decide (privateMatrixIntervalKey (h:=h) S T s j < privateMatrixIntervalKey (h:=h) S T s i ∧
        (if left then ¬(privateGraphInput pairs S T s).2.graph.Adj j i else True)) := by
  simp only [endpointEdge,privateRecords,List.getElem?_map,List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem j.isLt,Option.map_some,Option.getD_some]
  rw [retained_recordLT_correct pairs S T]
  rw [privateRecordAdj_correct]
  cases left <;> simp [privateMatrixIntervalKey,privateGraphInput,Enumeration.graphInput,
    Enumeration.matrixGraph, Complexity.MatrixGraph.graph]

end HiddenCircuits.GraphReduction.Runtime.PrivateInterval

namespace HiddenCircuits.GraphReduction.Runtime.PrivateInterval
open Complexity
open scoped BigOperators

lemma rowCount_card {n : ℕ} (edge : ℕ → ℕ → Bool) (P : Fin n → Prop) [DecidablePred P]
    (i : Fin n) (he : ∀ j : Fin n, edge i.val j.val=decide (P j)) :
    RankEmitter.rowCount edge i.val 0 n=(Finset.univ.filter P).card := by
  rw [RankEmitter.rowCount_sum,←List.range_eq_range',←List.map_coe_finRange_eq_range (n:=n)]
  simp only [List.map_map,Function.comp_def]
  rw [←Fin.sum_univ_def]
  simp only [he,decide_eq_true_eq,Finset.sum_boole,Nat.cast_id]

def endpoint (left : Bool) {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    Fin (privateGraphInput pairs S T s).1 → ℕ :=
  if left then (privateMatrixIntervalRepresentation pairs S T s).left
  else (privateMatrixIntervalRepresentation pairs S T s).right

lemma rowCount_correct {p h s : ℕ} (left : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (i : Fin (privateGraphInput pairs S T s).1) :
    RankEmitter.rowCount (endpointEdge left (privateRecords pairs S T s)) i.val 0
      (privateGraphInput pairs S T s).1 = endpoint left pairs S T s i := by
  rw [rowCount_card _ _ i (endpointEdge_correct left pairs S T i)]
  cases left <;> simp [endpoint,privateMatrixIntervalRepresentation,Interval.ofSuffixOrder,
    Interval.leftCount,Interval.rightCount]
  all_goals rfl

/-- The exact words the two physical scan emitters must serialize. -/
def bits (left : Bool) (records : List VertexRecord) : BitString :=
  RankEmitter.bits records.length (endpointEdge left records)

theorem bits_correct {p h s : ℕ} (left : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    bits left (privateRecords pairs S T s)=encodeBitList
      (List.ofFn (fun i => List.replicate (endpoint left pairs S T s i) true)) := by
  unfold bits RankEmitter.bits RankEmitter.words
  rw [privateRecords_length]
  rw [←List.map_coe_finRange_eq_range (n:=(privateGraphInput pairs S T s).1)]
  simp only [List.map_map,Function.comp_def,List.ofFn_eq_map]
  apply congrArg encodeBitList
  apply List.map_congr_left
  intro i _
  rw [rowCount_correct]
end HiddenCircuits.GraphReduction.Runtime.PrivateInterval
