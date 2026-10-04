import HiddenCircuits.Circuit.Runtime.BoundaryTransportEncoding
import HiddenCircuits.Complexity.RationalOracleEncoding

/-! Complete native constraint-circuit inputs include the wire count, the literal
gate list, and both logical boundary masks. Malformed encodings decode to none. -/
namespace HiddenCircuits.Complexity
open Circuit Circuit.Runtime

structure ConstraintInput where
  wires : ℕ
  gates : List (ConstraintGate wires)
  source : CodeBits wires
  target : CodeBits wires

def ConstraintInput.encode (C : ConstraintInput) : BitString := BoundaryTransport.inputBits C.gates C.source C.target
noncomputable def ConstraintInput.value (C : ConstraintInput) : ℚ := constraintCircuitMatrix C.gates C.source C.target

def decodeLogicalMask : (n : ℕ)→BitString→Option (CodeBits n)
  | 0,[]=>some PUnit.unit
  | n+1,b::bs=>(decodeLogicalMask n bs).map (fun x=>(finBitBool.symm b,x))
  | _,_=>none
@[simp] lemma decodeLogicalMask_mask (n : ℕ) (x : CodeBits n) :
    decodeLogicalMask n (BoundaryTransport.mask n x)=some x := by
  induction n with
  | zero=>cases x;rfl
  | succ n ih=>
    rcases x with ⟨i,x⟩
    fin_cases i <;> simp [BoundaryTransport.mask,decodeLogicalMask,finBitBool,ih]

def decodeConstraintGates (n : ℕ) : List BitString→Option (List (ConstraintGate n))
  | []=>some []
  | x::xs=>match decodeGate n x,decodeConstraintGates n xs with
    | some g,some gs=>some (g::gs)
    | _,_=>none
@[simp] lemma decodeConstraintGates_bits {n : ℕ} (w : List (ConstraintGate n)) :
    decodeConstraintGates n (w.map gateBits)=some w := by
  induction w with
  | nil=>rfl
  | cons g w ih=>simp [decodeConstraintGates,ih]

def ConstraintInput.decodePayload (n : ℕ) (source target payload : BitString) : Option ConstraintInput :=
  match decodeLogicalMask n source,decodeLogicalMask n target,decodeBitList payload with
  | some x,some y,some bytes=>match decodeConstraintGates n bytes with
    | some w=>some ⟨n,w,x,y⟩
    | none=>none
  | _,_,_=>none
def ConstraintInput.decode (raw : BitString) : Option ConstraintInput :=
  match unpairBits raw with
  | some (source,rest)=>match unpairBits rest with
    | some (target,circuit)=>match unpairBits circuit with
      | some (header,payload)=>if header=List.replicate header.length true then
          decodePayload header.length source target payload else none
      | none=>none
    | none=>none
  | none=>none
@[simp] lemma ConstraintInput.decode_encode (C : ConstraintInput) : ConstraintInput.decode C.encode=some C := by
  rcases C with ⟨n,w,x,y⟩
  simp only [ConstraintInput.encode,BoundaryTransport.inputBits,ConstraintInput.decode,circuitBits,unpair_pairBits,List.length_replicate,ite_true]
  simp [ConstraintInput.decodePayload]
def constraintEncoding : Computability.FinEncoding ConstraintInput where
  Γ:=Bool
  ΓFin:=inferInstance
  encode:=ConstraintInput.encode
  decode:=ConstraintInput.decode
  decode_encode:=ConstraintInput.decode_encode
lemma ConstraintInput.encode_injective : Function.Injective ConstraintInput.encode := constraintEncoding.encode_injective
noncomputable def constraintProblem (raw : BitString) : ℕ :=
  match ConstraintInput.decode raw with
  | none=>0
  | some C=>RationalOracleEncoding.code C.value
@[simp] lemma constraintProblem_encode (C : ConstraintInput) : constraintProblem C.encode=RationalOracleEncoding.code C.value := by
  simp [constraintProblem]
def ConstraintOracle (g : BitString→ℕ) : Prop := ∀C : ConstraintInput,g C.encode=RationalOracleEncoding.code C.value
lemma constraintProblem_oracle : ConstraintOracle constraintProblem := constraintProblem_encode
end HiddenCircuits.Complexity
