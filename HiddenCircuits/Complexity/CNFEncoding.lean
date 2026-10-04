import HiddenCircuits.Complexity.CNFQueryEncoding
import HiddenCircuits.Complexity.BitList

/-! Canonical binary arbitrary-CNF inputs. The declared variable count is retained,
so isolated variables contribute their correct certificate multiplicity. -/
namespace HiddenCircuits.Complexity

abbrev CNFInput := (n : ℕ) × (m : ℕ) × CNF n m

namespace CNF
variable {n m : ℕ}

def literalBits (l : Fin n × Bool) : BitString :=
  pairBits (List.replicate l.1.val true) [l.2]

def decodeLiteral (n : ℕ) (s : BitString) : Option (Fin n × Bool) :=
  match unpairBits s with
  | some (index,[sign]) =>
    if hi : index.length < n then
      if index = List.replicate index.length true then some (⟨index.length,hi⟩,sign) else none
    else none
  | _ => none

@[simp] theorem decodeLiteral_literalBits (l : Fin n × Bool) :
    decodeLiteral n (literalBits l) = some l := by
  rcases l with ⟨i,b⟩
  simp [decodeLiteral,literalBits,i.isLt]

def decodeLiterals (n : ℕ) : List BitString → Option (List (Fin n × Bool))
  | [] => some []
  | s::ss =>
    match decodeLiteral n s,decodeLiterals n ss with
    | some l,some ls => some (l::ls)
    | _,_ => none

@[simp] theorem decodeLiterals_literalBits (ls : List (Fin n × Bool)) :
    decodeLiterals n (ls.map literalBits) = some ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [decodeLiterals,ih]

def clauseBits (c : List (Fin n × Bool)) : BitString := encodeBitList (c.map literalBits)

def decodeClause (n : ℕ) (s : BitString) : Option (List (Fin n × Bool)) :=
  match decodeBitList s with
  | none => none
  | some ls => decodeLiterals n ls

@[simp] theorem decodeClause_clauseBits (c : List (Fin n × Bool)) :
    decodeClause n (clauseBits c) = some c := by simp [decodeClause,clauseBits]

def decodeClauses (n : ℕ) : List BitString → Option (List (List (Fin n × Bool)))
  | [] => some []
  | s::ss =>
    match decodeClause n s,decodeClauses n ss with
    | some c,some cs => some (c::cs)
    | _,_ => none

@[simp] theorem decodeClauses_clauseBits (cs : List (List (Fin n × Bool))) :
    decodeClauses n (cs.map clauseBits) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [decodeClauses,ih]

def bits (F : CNF n m) : BitString :=
  pairBits (List.replicate n true)
    (encodeBitList ((List.ofFn F.clause).map clauseBits))

end CNF

namespace CNFInput

def decodePayload (n : ℕ) (s : BitString) : Option CNFInput :=
  match decodeBitList s with
  | none => none
  | some bits =>
    match CNF.decodeClauses n bits with
    | none => none
    | some cs => some ⟨n,cs.length,⟨fun k => cs.get k⟩⟩

@[simp] theorem decodePayload_encode {n m : ℕ} (F : CNF n m) :
    decodePayload n (encodeBitList ((List.ofFn F.clause).map CNF.clauseBits)) =
      some ⟨n,m,F⟩ := by
  simp only [decodePayload,decodeBitList_encode,CNF.decodeClauses_clauseBits]
  have ht := (List.equivSigmaTuple (α := List (Fin n × Bool))).apply_symm_apply ⟨m,F.clause⟩
  exact congrArg (fun t : (k : ℕ) × (Fin k → List (Fin n × Bool)) =>
    (some ⟨n,t.1,⟨t.2⟩⟩ : Option CNFInput)) ht

def decode (s : BitString) : Option CNFInput :=
  match unpairBits s with
  | none => none
  | some (header,payload) =>
    if header = List.replicate header.length true then decodePayload header.length payload else none

def encode (F : CNFInput) : BitString := F.2.2.bits

@[simp] theorem decode_encode (F : CNFInput) : decode (encode F) = some F := by
  rcases F with ⟨n,m,F⟩
  simp only [decode,encode,CNF.bits,unpair_pairBits,List.length_replicate,ite_true]
  exact decodePayload_encode F

def encoding : Computability.FinEncoding CNFInput where
  Γ := Bool
  ΓFin := inferInstance
  encode := encode
  decode := decode
  decode_encode := decode_encode

theorem encode_injective : Function.Injective encode := encoding.encode_injective

/-- Malformed strings have answer zero. Variable count is explicit even if a
variable occurs in no clause. -/
noncomputable def satProblem (s : BitString) : ℕ :=
  match decode s with
  | none => 0
  | some F => F.2.2.satCount

@[simp] theorem satProblem_encode (F : CNFInput) : satProblem (encode F) = F.2.2.satCount := by
  simp [satProblem]

theorem encode_length_lower (F : CNFInput) : 2*F.1+F.2.1+1 ≤ (encode F).length := by
  rcases F with ⟨n,m,F⟩
  simp only [encode,CNF.bits,pairBits_length,List.length_replicate,encodeBitList_length,
    List.length_map,List.length_ofFn]
  omega

/-- The actual binary source length controls every binary target query length. -/
theorem query_length_in_source_bits (F : CNFInput) (i : Fin (F.1+1)) (j : Fin (F.2.1+1)) :
    (F.2.2.encodedCloneQuery i.val j.val).length ≤ (encode F).length^4 :=
  (F.2.2.encodedCloneQuery_grid_length i j).trans
    (Nat.pow_le_pow_left (encode_length_lower F) 4)

end CNFInput
end HiddenCircuits.Complexity
