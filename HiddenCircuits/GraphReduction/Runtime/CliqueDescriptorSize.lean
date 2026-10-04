import HiddenCircuits.GraphReduction.Runtime.CliqueEmitter

namespace HiddenCircuits.GraphReduction.Runtime
open Complexity

lemma unitVertexRecord_bounds {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (v : UnitQueryVertex p h s S T) :
    (unitVertexRecord pairs v).layer≤h ∧ (unitVertexRecord pairs v).track≤2*p+s ∧ (unitVertexRecord pairs v).cut.index≤2*p := by
  rcases v with (v|v)|v
  · simp only [unitVertexRecord,backgroundCode];exact ⟨by omega,by omega,by omega⟩
  · simp only [unitVertexRecord];exact ⟨by omega,by omega,cutCode_index_le _⟩
  · simp only [unitVertexRecord,backgroundCode];exact ⟨by omega,by omega,by omega⟩
lemma privateVertexRecord_bounds {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (v : PrivateQueryVertex p h s S T) :
    (privateVertexRecord pairs v).layer≤h ∧ (privateVertexRecord pairs v).track≤2*p+s ∧ (privateVertexRecord pairs v).cut.index≤2*p := by
  rcases v with (v|v)|(⟨v|v,q⟩)
  · simp only [privateVertexRecord,backgroundCode];exact ⟨by omega,by omega,by omega⟩
  · simp only [privateVertexRecord];exact ⟨by omega,by omega,cutCode_index_le _⟩
  · simp only [privateVertexRecord,backgroundCode];exact ⟨by omega,by omega,by omega⟩
  · simp only [privateVertexRecord,backgroundCode];exact ⟨by omega,by omega,by omega⟩

namespace CliqueEmitter
lemma descriptor_size {p h : ℕ} (mode : Bool) (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    (descriptor mode pairs S T s).length≤(graphInput mode pairs S T s).1*(18+4*h+12*p+4*s) := by
  have hr : ∀v∈records mode pairs S T s,(encodeVertex v).length≤8+2*h+6*p+2*s := by
    intro v hv
    cases mode
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      have hb := unitVertexRecord_bounds pairs S T x
      rw [encodeVertex_length]
      omega
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      have hb := privateVertexRecord_bounds pairs S T x
      rw [encodeVertex_length]
      omega
  have hb := encoded_records_length_le (records mode pairs S T s) (8+2*h+6*p+2*s) hr
  rw [records_length] at hb
  simpa only [descriptor,show 2*(8+2*h+6*p+2*s)+2=18+4*h+12*p+4*s by omega] using hb
end CliqueEmitter
end HiddenCircuits.GraphReduction.Runtime
