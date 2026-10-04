import HiddenCircuits.Complexity.DeltaEncoding
import HiddenCircuits.Complexity.EvalEncodingSoundness

/-! Native logical-circuit successful decodes reconstruct their exact input bytes,
including boundary masks, every gate marker and the full strict list payload. -/
namespace HiddenCircuits.Complexity
open Circuit Circuit.Runtime
set_option maxHeartbeats 600000

lemma logicalMask_of_decode {n : ℕ} {xs : BitString} {x : CodeBits n}
    (h : decodeLogicalMask n xs=some x) : BoundaryTransport.mask n x=xs := by
  induction n generalizing xs with
  | zero=>cases xs <;> simp [decodeLogicalMask] at h;cases h;rfl
  | succ n ih=>
    cases xs with
    | nil=>simp [decodeLogicalMask] at h
    | cons b xs=>
      cases ht:decodeLogicalMask n xs with
      | none=>simp [decodeLogicalMask,ht] at h
      | some t=>
        simp only [decodeLogicalMask,ht,Option.map_some,Option.some.injEq] at h
        subst x
        have hi:=ih ht
        cases b <;> simp [BoundaryTransport.mask,finBitBool,hi]
lemma decodeLogicalMask_isSome (n : ℕ) (xs : BitString) :
    (decodeLogicalMask n xs).isSome=true ↔ xs.length=n := by
  induction n generalizing xs with
  | zero=>cases xs <;> simp [decodeLogicalMask]
  | succ n ih=>
    cases xs with
    | nil=>simp [decodeLogicalMask]
    | cons b xs=>simp [decodeLogicalMask,ih]
lemma gateTag_bits_of_decode {xs : BitString} {t : GateTag} (h : decodeTag xs=some t) : t.bits=xs := by
  unfold decodeTag at h
  split at h <;> cases h <;> rfl
lemma gateFromTag_bits (n : ℕ) (t : GateTag) (p : ℕ) (h : p+t.width ≤ n) :
    gateBits (gateFromTag n t p h)=pairBits t.bits (List.replicate p true) := by cases t <;> rfl
lemma gateBits_of_decode {n : ℕ} {xs : BitString} {a : ConstraintGate n}
    (h : decodeGate n xs=some a) : gateBits a=xs := by
  unfold decodeGate at h
  cases hu:unpairBits xs with
  | none=>simp [hu] at h
  | some p=>
    rcases p with ⟨tag,pos⟩
    simp only [hu] at h
    cases ht:decodeTag tag with
    | none=>simp [ht] at h
    | some t=>
      simp only [ht] at h
      split_ifs at h with hb hp
      cases h
      rw [gateFromTag_bits,gateTag_bits_of_decode ht,←hp]
      exact pairBits_of_unpair _ _ _ hu
lemma gateBits_of_decodeConstraintGates {n : ℕ} (xs : List BitString) (w : List (ConstraintGate n))
    (h : decodeConstraintGates n xs=some w) : w.map gateBits=xs := by
  induction xs generalizing w with
  | nil=>simp [decodeConstraintGates] at h;subst w;rfl
  | cons x xs ih=>
    cases hg:decodeGate n x with
    | none=>simp [decodeConstraintGates,hg] at h
    | some g=>
      cases ht:decodeConstraintGates n xs with
      | none=>simp [decodeConstraintGates,hg,ht] at h
      | some t=>
        simp only [decodeConstraintGates,hg,ht,Option.some.injEq] at h
        subst w
        simp only [List.map_cons,gateBits_of_decode hg,ih t ht]
lemma ConstraintInput.encode_of_decode {xs : BitString} {C : ConstraintInput}
    (h : ConstraintInput.decode xs=some C) : C.encode=xs := by
  unfold ConstraintInput.decode at h
  cases h₁:unpairBits xs with
  | none=>simp [h₁] at h
  | some p₁=>
    rcases p₁ with ⟨source,rest⟩
    simp only [h₁] at h
    cases h₂:unpairBits rest with
    | none=>simp [h₂] at h
    | some p₂=>
      rcases p₂ with ⟨target,circuit⟩
      simp only [h₂] at h
      cases h₃:unpairBits circuit with
      | none=>simp [h₃] at h
      | some p₃=>
        rcases p₃ with ⟨header,payload⟩
        simp only [h₃] at h
        split_ifs at h with hh
        unfold ConstraintInput.decodePayload at h
        cases hs:decodeLogicalMask header.length source with
        | none=>simp [hs] at h
        | some x=>
          cases ht:decodeLogicalMask header.length target with
          | none=>simp [hs,ht] at h
          | some y=>
            cases hb:decodeBitList payload with
            | none=>simp [hs,ht,hb] at h
            | some bytes=>
              cases hw:decodeConstraintGates header.length bytes with
              | none=>simp [hs,ht,hb,hw] at h
              | some w=>
                simp only [hs,ht,hb,hw,Option.some.injEq] at h
                subst C
                simp only [ConstraintInput.encode,BoundaryTransport.inputBits,circuitBits]
                rw [logicalMask_of_decode hs,logicalMask_of_decode ht,←hh,
                  gateBits_of_decodeConstraintGates bytes w hw,encodeBitList_of_decode payload bytes hb,
                  pairBits_of_unpair _ _ _ h₃,pairBits_of_unpair _ _ _ h₂,pairBits_of_unpair _ _ _ h₁]
lemma descriptor_of_decodeDeltaGate {n : ℕ} {a : ConstraintGate n} {d : DeltaGate n}
    (h : decodeDeltaGate a=some d) : Complexity.DeltaGate.descriptor d=a := by
  cases a <;> simp [decodeDeltaGate] at h <;> cases h <;> rfl
lemma descriptors_of_decodeDeltaGates {n : ℕ} (w : List (ConstraintGate n)) (d : List (DeltaGate n))
    (h : decodeDeltaGates w=some d) : d.map Complexity.DeltaGate.descriptor=w := by
  induction w generalizing d with
  | nil=>simp [decodeDeltaGates] at h;subst d;rfl
  | cons a w ih=>
    cases hg:decodeDeltaGate a with
    | none=>simp [decodeDeltaGates,hg] at h
    | some g=>
      cases ht:decodeDeltaGates w with
      | none=>simp [decodeDeltaGates,hg,ht] at h
      | some t=>
        simp only [decodeDeltaGates,hg,ht,Option.some.injEq] at h
        subst d
        simp only [List.map_cons,descriptor_of_decodeDeltaGate hg,ih t ht]
lemma DeltaInput.encode_of_decode {xs : BitString} {C : DeltaInput}
    (h : DeltaInput.decode xs=some C) : C.encode=xs := by
  unfold DeltaInput.decode at h
  cases hc:ConstraintInput.decode xs with
  | none=>simp [hc] at h
  | some D=>
    cases hw:decodeDeltaGates D.gates with
    | none=>simp [hc,hw] at h
    | some w=>
      simp only [hc,hw,Option.some.injEq] at h
      subst C
      simp only [DeltaInput.encode,DeltaInput.descriptor,descriptors_of_decodeDeltaGates D.gates w hw]
      exact ConstraintInput.encode_of_decode hc
end HiddenCircuits.Complexity
