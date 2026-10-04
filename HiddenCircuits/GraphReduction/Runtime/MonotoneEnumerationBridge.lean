import HiddenCircuits.GraphReduction.Runtime.DescriptorEnumeration
import HiddenCircuits.GraphReduction.Runtime.DescriptorOdd

/-! Fresh exact enumeration bridge for the physically emitted monotone query
records. The order is retained even vertices, false-side probes, cut-tagged odd
vertices, and true-side probes, including the coincident-boundary case. -/
namespace HiddenCircuits.GraphReduction.Runtime.DescriptorEnumeration
open Complexity
set_option maxHeartbeats 800000

lemma odd_records_eq_finRange {p : ℕ} (width layer : ℕ) (ps : List (CutPair p)) :
    DescriptorOdd.records width layer ps =
      (List.finRange ps.length).flatMap (fun i => (List.finRange width).map (fun j =>
        (⟨true,false,layer+i.val,j.val,cutCode (ps.get i)⟩ : VertexRecord))) := by
  induction ps generalizing layer with
  | nil => simp [DescriptorOdd.records]
  | cons P ps ih =>
    rw [DescriptorOdd.records, row_eq_finRange, ih]
    simp only [List.length_cons, List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    simp [DescriptorOdd.vertex,Nat.add_comm,Nat.add_left_comm]

lemma odd_records_ofFn {p h : ℕ} (width layer : ℕ) (pairs : Fin h → CutPair p) :
    DescriptorOdd.records width layer (List.ofFn pairs) =
      (List.finRange h).flatMap (fun i => (List.finRange width).map (fun j =>
        (⟨true,false,layer+i.val,j.val,cutCode (pairs i)⟩ : VertexRecord))) := by
  induction h generalizing layer with
  | zero => simp [DescriptorOdd.records]
  | succ n ih =>
    rw [List.ofFn_succ,DescriptorOdd.records,row_eq_finRange,ih,List.finRange_succ]
    simp [DescriptorOdd.vertex,List.flatMap_map,Nat.add_comm,Nat.add_left_comm]

lemma odd_labels_eq {p h : ℕ} (pairs : Fin h → CutPair p) :
    (oddEnumeration (2*p) h).labels.map
      (fun x => (⟨true,false,x.1.val,x.2.val,cutCode (pairs x.1)⟩ : VertexRecord)) =
    DescriptorOdd.records (2*p) 0 (List.ofFn pairs) := by
  rw [odd_records_ofFn]
  simp [oddEnumeration,Enumeration.prod,Enumeration.fin,List.product,List.map_flatMap,
    List.map_map,Function.comp_def]

theorem monotoneRecords_eq {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    monotoneRecords pairs S T s =
      DescriptorEven.records (2*p) h (stateBits S) (stateBits T) ++
      DescriptorRectangle.records ⟨false,true,0,0,backgroundCode⟩ s h ++
      DescriptorOdd.records (2*p) 0 (List.ofFn pairs) ++
      DescriptorRectangle.records ⟨true,true,0,0,backgroundCode⟩ s h := by
  simp only [monotoneRecords,monotoneEnumeration,Enumeration.sum,List.map_append,
    List.map_map,Function.comp_def,vertexRecord]
  rw [retained_even_eq,probe_labels_eq,odd_labels_eq,probe_labels_eq]
  simp only [List.append_assoc]

theorem monotoneRecords_list_eq {p : ℕ} (ps : List (CutPair p))
    (S T : State (2*p) p) (s : ℕ) :
    monotoneRecords (fun i=>ps.get i) S T s =
      DescriptorEven.records (2*p) ps.length (stateBits S) (stateBits T) ++
      DescriptorRectangle.records ⟨false,true,0,0,backgroundCode⟩ s ps.length ++
      DescriptorOdd.records (2*p) 0 ps ++
      DescriptorRectangle.records ⟨true,true,0,0,backgroundCode⟩ s ps.length := by
  simpa using monotoneRecords_eq (fun i=>ps.get i) S T s

/-- When both boundaries coincide, only source tracks absent from the target
survive; there are no odd vertices or probe rows. -/
theorem monotoneRecords_zero {p : ℕ} (pairs : Fin 0 → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    monotoneRecords pairs S T s = DescriptorMaskRow.records (DescriptorEven.vertex 0)
      (DescriptorMaskDifference.difference (stateBits S) (stateBits T)) := by
  simp [monotoneRecords_eq,DescriptorEven.records,DescriptorRectangle.records,DescriptorOdd.records]

end HiddenCircuits.GraphReduction.Runtime.DescriptorEnumeration
