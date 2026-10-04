import HiddenCircuits.GraphReduction.Runtime.CliqueFront
import HiddenCircuits.GraphReduction.Runtime.CliqueDescriptor
import HiddenCircuits.GraphReduction.Runtime.MonotoneEnumerationBridge

namespace HiddenCircuits.GraphReduction.Runtime.CliqueFront
open Complexity DescriptorEnumeration
set_option maxHeartbeats 700000

lemma unitRecords_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    unitRecords (fun i=>ps.get i) S T s=records false ps (stateBits S) (stateBits T) s := by
  simp only [unitRecords,unitEnumeration,Enumeration.sum,List.map_append,List.map_map,Function.comp_def,unitVertexRecord]
  rw [retained_even_eq,odd_labels_eq,probe_labels_eq]
  simp [records,tailRecords,DescriptorFront.taggedVertex]

lemma privateRecords_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    privateRecords (fun i=>ps.get i) S T s=records true ps (stateBits S) (stateBits T) s := by
  simp only [privateRecords,privateEnumeration,Enumeration.sum,List.map_append,List.map_map,Function.comp_def,privateVertexRecord]
  rw [retained_even_eq,odd_labels_eq]
  simp only [records,tailRecords,ite_true,List.ofFn_get]
  rw [rectangle_eq_finRange,rectangle_eq_finRange]
  simp [Enumeration.prod,Enumeration.sum,Enumeration.fin,List.product,List.map_flatMap,List.flatMap_map,List.flatMap_append,
    List.map_map,Function.comp_def,privateVertexRecord,DescriptorFront.taggedVertex,List.append_assoc]

lemma descriptor_false_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    descriptor false ps (stateBits S) (stateBits T) s=unitDescriptor (fun i=>ps.get i) S T s := by
  rw [descriptor,←unitRecords_eq]
  rfl
lemma descriptor_true_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    descriptor true ps (stateBits S) (stateBits T) s=privateDescriptor (fun i=>ps.get i) S T s := by
  rw [descriptor,←privateRecords_eq]
  rfl
end HiddenCircuits.GraphReduction.Runtime.CliqueFront
