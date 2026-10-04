import HiddenCircuits.Complexity.NativeValidation.Semantics
import HiddenCircuits.Complexity.NativeEncodingSoundness

namespace HiddenCircuits.Complexity.NativeValidation.Semantics
open Circuit Circuit.Runtime GraphVerifier
set_option maxHeartbeats 600000

lemma parse_reconstruct (xs : BitString) (h : (parse xs).ok=true) :
    pairBits (parse xs).left (parse xs).right=xs := by
  apply pairBits_of_unpair
  rw [parse_spec,h]
  rfl
lemma validList_witness {G : Type*} (mode : Bool) (width xs : BitString) (bits : G→BitString)
    (hgate : ∀bs,Gate.valid mode bs width=true→∃g,bits g=bs)
    (h : validList mode width xs=true) : ∃w : List G,encodeBitList (w.map bits)=xs := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih=>
    cases xs with
    | nil=>exact ⟨[],rfl⟩
    | cons b bs=>
      rw [validList] at h
      simp only [Bool.and_eq_true] at h
      have ho : (parse bs).ok=true := by aesop
      have hb : b=true := by aesop
      have hg : Gate.valid mode (parse bs).left width=true := by aesop
      have ht : validList mode width (parse bs).right=true := by aesop
      subst b
      obtain ⟨g,hg⟩:=hgate _ hg
      obtain ⟨w,hw⟩:=ih (parse bs).right (EvalValidation.Field.tail_shorter true bs) ht
      refine ⟨g::w,?_⟩
      simp only [List.map_cons,encodeBitList,hg,hw,parse_reconstruct bs ho]
lemma validList_encode {G : Type*} (mode : Bool) (width : BitString) (bits : G→BitString)
    (hgate : ∀g,Gate.valid mode (bits g) width=true) (w : List G) :
    validList mode width (encodeBitList (w.map bits))=true := by
  induction w with
  | nil=>simp [encodeBitList,validList]
  | cons g w ih=>simp [List.map_cons,encodeBitList,validList,parse_pair,hgate,ih]
lemma test_components (mode : Bool) (xs : BitString) : test mode xs=true ↔
    validList mode (header xs) (payload xs)=true ∧
    (target xs).length=(header xs).length ∧ (source xs).length=(header xs).length ∧
    (header xs).all id=true ∧ (third xs).ok=true ∧ (second xs).ok=true ∧ (first xs).ok=true := by
  simp [test,flags,Bool.and_assoc]
lemma test_rawWitness {G : Type*} (mode : Bool) (xs : BitString) (bits : G→BitString)
    (hgate : ∀bs,Gate.valid mode bs (header xs)=true→∃g,bits g=bs)
    (h : test mode xs=true) :
    ∃x y : CodeBits (header xs).length, ∃w : List G,
      pairBits (BoundaryTransport.mask _ x) (pairBits (BoundaryTransport.mask _ y)
        (pairBits (List.replicate (header xs).length true) (encodeBitList (w.map bits))))=xs := by
  obtain ⟨hl,ht,hs,hu,h₃,h₂,h₁⟩:=(test_components mode xs).mp h
  have hx:(decodeLogicalMask (header xs).length (source xs)).isSome=true := (decodeLogicalMask_isSome _ _).mpr hs
  have hy:(decodeLogicalMask (header xs).length (target xs)).isSome=true := (decodeLogicalMask_isSome _ _).mpr ht
  cases hxd:decodeLogicalMask (header xs).length (source xs) with
  | none=>simp [hxd] at hx
  | some x=>
    cases hyd:decodeLogicalMask (header xs).length (target xs) with
    | none=>simp [hyd] at hy
    | some y=>
      obtain ⟨w,hw⟩:=validList_witness mode (header xs) (payload xs) bits hgate hl
      refine ⟨x,y,w,?_⟩
      rw [logicalMask_of_decode hxd,logicalMask_of_decode hyd,hw,←(GraphVerifier.header_all_true _).mp hu]
      have hc:=parse_reconstruct (second xs).right h₃
      change pairBits (header xs) (payload xs)=(second xs).right at hc
      rw [hc]
      have ht:=parse_reconstruct (first xs).right h₂
      change pairBits (target xs) (second xs).right=(first xs).right at ht
      rw [ht]
      exact parse_reconstruct xs h₁
lemma test_canonical {G : Type*} (mode : Bool) (n : ℕ) (bits : G→BitString)
    (hgate : ∀g,Gate.valid mode (bits g) (List.replicate n true)=true)
    (w : List G) (x y : CodeBits n) :
    test mode (pairBits (BoundaryTransport.mask n x) (pairBits (BoundaryTransport.mask n y)
      (pairBits (List.replicate n true) (encodeBitList (w.map bits)))))=true := by
  have hl:=validList_encode mode (List.replicate n true) bits hgate w
  simp [test,flags,source,target,header,payload,first,second,third,parse_pair,hl]
end HiddenCircuits.Complexity.NativeValidation.Semantics
