import HiddenCircuits.Circuit.RestoringSource
import HiddenCircuits.Complexity.BitList

/-! Canonical finite constraint-gate bytes: a fixed four-bit kind and the unary
left placement index. The wire count in the enclosing stream determines the
remaining placement uniquely. -/
namespace HiddenCircuits.Circuit.Runtime
open HiddenCircuits.Complexity

inductive GateTag | reset | copy | scale | signScale | swap | hadamard | mix | forbid | controlledSign | encodedSwap
  deriving DecidableEq, Fintype

def GateTag.bits : GateTag → BitString
  | .reset => [false,false,false,false]
  | .copy => [false,false,false,true]
  | .scale => [false,false,true,false]
  | .signScale => [false,false,true,true]
  | .swap => [false,true,false,false]
  | .hadamard => [false,true,false,true]
  | .mix => [false,true,true,false]
  | .forbid => [false,true,true,true]
  | .controlledSign => [true,false,false,false]
  | .encodedSwap => [true,false,false,true]

def decodeTag : BitString → Option GateTag
  | [false,false,false,false] => some .reset
  | [false,false,false,true] => some .copy
  | [false,false,true,false] => some .scale
  | [false,false,true,true] => some .signScale
  | [false,true,false,false] => some .swap
  | [false,true,false,true] => some .hadamard
  | [false,true,true,false] => some .mix
  | [false,true,true,true] => some .forbid
  | [true,false,false,false] => some .controlledSign
  | [true,false,false,true] => some .encodedSwap
  | _ => none

@[simp] theorem decodeTag_bits (t : GateTag) : decodeTag t.bits=some t := by cases t <;> rfl
@[simp] theorem GateTag.bits_length (t : GateTag) : t.bits.length=4 := by cases t <;> rfl

def GateTag.width : GateTag → ℕ | .forbid | .controlledSign => 2 | _ => 1

def gateTag {n : ℕ} : ConstraintGate n → GateTag
  | .one _ .reset => .reset
  | .one _ .copy => .copy
  | .one _ .scale => .scale
  | .one _ .signScale => .signScale
  | .one _ .swap => .swap
  | .one _ .hadamard => .hadamard
  | .one _ .mix => .mix
  | .one _ .encodedSwap => .encodedSwap
  | .forbid _ => .forbid
  | .controlledSign _ => .controlledSign

def gatePosition {n : ℕ} : ConstraintGate n → ℕ
  | .one p _ => p.before
  | .forbid p => p.before
  | .controlledSign p => p.before

def gateFromTag (n : ℕ) (t : GateTag) (b : ℕ) (h : b+t.width≤n) : ConstraintGate n :=
  match t with
  | .reset => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .reset
  | .copy => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .copy
  | .scale => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .scale
  | .signScale => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .signScale
  | .swap => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .swap
  | .hadamard => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .hadamard
  | .mix => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .mix
  | .encodedSwap => .one ⟨b,n-b-1,by dsimp [GateTag.width] at h;omega⟩ .encodedSwap
  | .forbid => .forbid ⟨b,n-b-2,by dsimp [GateTag.width] at h;omega⟩
  | .controlledSign => .controlledSign ⟨b,n-b-2,by dsimp [GateTag.width] at h;omega⟩

def gateBits {n : ℕ} (g : ConstraintGate n) : BitString :=
  pairBits (gateTag g).bits (List.replicate (gatePosition g) true)

def decodeGate (n : ℕ) (s : BitString) : Option (ConstraintGate n) :=
  match unpairBits s with
  | some (kb,ib) => match decodeTag kb with
    | none => none
    | some t => if h : ib.length+t.width≤n then
        if ib=List.replicate ib.length true then some (gateFromTag n t ib.length h) else none
      else none
  | none => none

lemma gatePosition_bound {n : ℕ} (g : ConstraintGate n) : gatePosition g+(gateTag g).width≤n := by
  cases g with
  | one p g => have hp:=p.size;cases g <;> dsimp [gatePosition,gateTag,GateTag.width] <;> omega
  | forbid p => have hp:=p.size;dsimp [gatePosition,gateTag,GateTag.width];omega
  | controlledSign p => have hp:=p.size;dsimp [gatePosition,gateTag,GateTag.width];omega

lemma gateFromTag_self {n : ℕ} (g : ConstraintGate n) :
    gateFromTag n (gateTag g) (gatePosition g) (gatePosition_bound g)=g := by
  cases g with
  | one p g =>
    rcases p with ⟨b,a,h⟩
    have he : n-b-1=a := by omega
    cases g <;> simp [gateFromTag,gateTag,gatePosition,he]
  | forbid p =>
    rcases p with ⟨b,a,h⟩
    have he : n-b-2=a := by omega
    simp [gateFromTag,gateTag,gatePosition,he]
  | controlledSign p =>
    rcases p with ⟨b,a,h⟩
    have he : n-b-2=a := by omega
    simp [gateFromTag,gateTag,gatePosition,he]

@[simp] theorem decodeGate_gateBits {n : ℕ} (g : ConstraintGate n) : decodeGate n (gateBits g)=some g := by
  simp [decodeGate,gateBits,gatePosition_bound,gateFromTag_self]

@[simp] theorem gateBits_length {n : ℕ} (g : ConstraintGate n) : (gateBits g).length=gatePosition g+9 := by
  simp [gateBits]
  omega

def circuitBits (n : ℕ) (gates : List (ConstraintGate n)) : BitString :=
  pairBits (List.replicate n true) (encodeBitList (gates.map gateBits))

end HiddenCircuits.Circuit.Runtime
