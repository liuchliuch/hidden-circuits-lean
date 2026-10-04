import HiddenCircuits.Complexity.NativeValidation.SemanticsModel
import HiddenCircuits.Complexity.NativeValidation.GateSoundness

/-! The complete actual native validator accepts exactly successful decodes;
there is no supplied well-formedness or serialization certificate. -/
namespace HiddenCircuits.Complexity.NativeValidation.Semantics
open Circuit Circuit.Runtime GraphVerifier
set_option maxHeartbeats 600000

lemma constraint_gate_witness (n : ℕ) (width : BitString) (hw : width.length=n) (bs : BitString)
    (h : Gate.valid false bs width=true) : ∃g : ConstraintGate n,gateBits g=bs := by
  rw [Gate.valid_decode false n bs width hw] at h
  unfold Gate.decoded at h
  cases hg:decodeGate n bs with
  | none=>simp [hg] at h
  | some g=>exact ⟨g,gateBits_of_decode hg⟩
lemma delta_gate_witness (n : ℕ) (width : BitString) (hw : width.length=n) (bs : BitString)
    (h : Gate.valid true bs width=true) : ∃g : DeltaGate n,gateBits (Complexity.DeltaGate.descriptor g)=bs := by
  rw [Gate.valid_decode true n bs width hw] at h
  unfold Gate.decoded at h
  cases hg:decodeGate n bs with
  | none=>simp [hg] at h
  | some g=>
    cases hd:decodeDeltaGate g with
    | none=>simp [hg,hd] at h
    | some d=>exact ⟨d,by rw [descriptor_of_decodeDeltaGate hd];exact gateBits_of_decode hg⟩
lemma test_constraint_sound (xs : BitString) (h : test false xs=true) :
    (ConstraintInput.decode xs).isSome=true := by
  obtain ⟨x,y,w,hw⟩:=test_rawWitness false xs (@gateBits (header xs).length)
    (constraint_gate_witness _ _ rfl) h
  let C : ConstraintInput:=⟨(header xs).length,w,x,y⟩
  have he:C.encode=xs:=hw
  rw [←he,ConstraintInput.decode_encode];rfl
lemma test_delta_sound (xs : BitString) (h : test true xs=true) :
    (DeltaInput.decode xs).isSome=true := by
  obtain ⟨x,y,w,hw⟩:=test_rawWitness true xs
    (fun g : DeltaGate (header xs).length=>gateBits (Complexity.DeltaGate.descriptor g))
    (delta_gate_witness _ _ rfl) h
  let C : DeltaInput:=⟨(header xs).length,w,x,y⟩
  have he:C.encode=xs:=by simpa [C,DeltaInput.encode,DeltaInput.descriptor,ConstraintInput.encode,BoundaryTransport.inputBits,circuitBits,List.map_map,Function.comp_def] using hw
  rw [←he,DeltaInput.decode_encode];rfl
lemma test_constraint_encode (C : ConstraintInput) : test false C.encode=true := by
  apply test_canonical false C.wires gateBits _ C.gates C.source C.target
  intro g
  rw [Gate.valid_decode false C.wires (gateBits g) (List.replicate C.wires true) (by simp)]
  simp [Gate.decoded]
lemma test_delta_encode (C : DeltaInput) : test true C.encode=true := by
  change test true (pairBits (BoundaryTransport.mask C.wires C.source) (pairBits (BoundaryTransport.mask C.wires C.target)
    (pairBits (List.replicate C.wires true) (encodeBitList ((C.gates.map Complexity.DeltaGate.descriptor).map gateBits)))))=true
  rw [List.map_map]
  apply test_canonical true C.wires (fun g=>gateBits (Complexity.DeltaGate.descriptor g)) _ C.gates C.source C.target
  intro g
  rw [Gate.valid_decode true C.wires _ _ (by simp)]
  simp [Gate.decoded]

theorem test_constraint_decode (xs : BitString) : test false xs=(ConstraintInput.decode xs).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact test_constraint_sound xs
  · intro h
    cases hd:ConstraintInput.decode xs with
    | none=>simp [hd] at h
    | some C=>rw [←ConstraintInput.encode_of_decode hd];exact test_constraint_encode C
theorem test_delta_decode (xs : BitString) : test true xs=(DeltaInput.decode xs).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact test_delta_sound xs
  · intro h
    cases hd:DeltaInput.decode xs with
    | none=>simp [hd] at h
    | some C=>rw [←DeltaInput.encode_of_decode hd];exact test_delta_encode C
end HiddenCircuits.Complexity.NativeValidation.Semantics
