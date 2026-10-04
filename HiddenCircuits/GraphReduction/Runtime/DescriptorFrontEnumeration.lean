import HiddenCircuits.GraphReduction.Runtime.DescriptorFront
import HiddenCircuits.GraphReduction.Runtime.MonotoneEnumerationBridge

namespace HiddenCircuits.GraphReduction.Runtime.DescriptorFront
open Complexity

lemma records_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    records ps (stateBits S) (stateBits T) s=monotoneRecords (fun i=>ps.get i) S T s :=
  (DescriptorEnumeration.monotoneRecords_list_eq ps S T s).symm
lemma descriptor_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    descriptor ps (stateBits S) (stateBits T) s=monotoneDescriptor (fun i=>ps.get i) S T s := by
  rw [descriptor,records_eq]
  rfl
lemma count_eq {p : ℕ} (ps : List (CutPair p)) (S T : State (2*p) p) (s : ℕ) :
    (records ps (stateBits S) (stateBits T) s).length=(monotoneGraphInput (fun i=>ps.get i) S T s).1 := by
  rw [records_eq,monotoneRecords_length]
end HiddenCircuits.GraphReduction.Runtime.DescriptorFront
