import HiddenCircuits.Complexity.ConstraintEncoding

/-! Native Δ-circuit inputs use exactly the shared logical gate encoding; the
constraint tag denotes Δ here. The N/CZ-only second constraint tag is rejected. -/
namespace HiddenCircuits.Complexity
open Circuit Circuit.Runtime

structure DeltaInput where
  wires : ℕ
  gates : List (DeltaGate wires)
  source : CodeBits wires
  target : CodeBits wires

def DeltaGate.descriptor {n : ℕ} : DeltaGate n→ConstraintGate n
  | .one p g=>.one p g
  | .constraint p=>.forbid p
def decodeDeltaGate {n : ℕ} : ConstraintGate n→Option (DeltaGate n)
  | .one p g=>some (.one p g)
  | .forbid p=>some (.constraint p)
  | .controlledSign _=>none
@[simp] lemma decodeDeltaGate_descriptor {n : ℕ} (g : DeltaGate n) : decodeDeltaGate (DeltaGate.descriptor g)=some g := by cases g <;> rfl

def decodeDeltaGates {n : ℕ} : List (ConstraintGate n)→Option (List (DeltaGate n))
  | []=>some []
  | x::xs=>match decodeDeltaGate x,decodeDeltaGates xs with
    | some g,some gs=>some (g::gs)
    | _,_=>none
@[simp] lemma decodeDeltaGates_descriptors {n : ℕ} (w : List (DeltaGate n)) :
    decodeDeltaGates (w.map DeltaGate.descriptor)=some w := by
  induction w with
  | nil=>rfl
  | cons g w ih=>simp [decodeDeltaGates,ih]

def DeltaInput.descriptor (C : DeltaInput) : ConstraintInput := ⟨C.wires,C.gates.map DeltaGate.descriptor,C.source,C.target⟩
def DeltaInput.encode (C : DeltaInput) : BitString := C.descriptor.encode
noncomputable def DeltaInput.value (C : DeltaInput) : ℚ := deltaCircuitMatrix C.gates C.source C.target

def DeltaInput.decode (raw : BitString) : Option DeltaInput :=
  match ConstraintInput.decode raw with
  | none=>none
  | some C=>match decodeDeltaGates C.gates with
    | none=>none
    | some w=>some ⟨C.wires,w,C.source,C.target⟩
@[simp] lemma DeltaInput.decode_encode (C : DeltaInput) : DeltaInput.decode C.encode=some C := by
  rcases C with ⟨n,w,x,y⟩
  simp [DeltaInput.decode,DeltaInput.encode,DeltaInput.descriptor]
def deltaEncoding : Computability.FinEncoding DeltaInput where
  Γ:=Bool
  ΓFin:=inferInstance
  encode:=DeltaInput.encode
  decode:=DeltaInput.decode
  decode_encode:=DeltaInput.decode_encode
lemma DeltaInput.encode_injective : Function.Injective DeltaInput.encode := deltaEncoding.encode_injective
noncomputable def deltaProblem (raw : BitString) : ℕ :=
  match DeltaInput.decode raw with
  | none=>0
  | some C=>RationalOracleEncoding.code C.value
@[simp] lemma deltaProblem_encode (C : DeltaInput) : deltaProblem C.encode=RationalOracleEncoding.code C.value := by simp [deltaProblem]
def DeltaOracle (g : BitString→ℕ) : Prop := ∀C : DeltaInput,g C.encode=RationalOracleEncoding.code C.value
lemma deltaProblem_oracle : DeltaOracle deltaProblem := deltaProblem_encode
end HiddenCircuits.Complexity
