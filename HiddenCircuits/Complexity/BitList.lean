import HiddenCircuits.Complexity.SharpP

/-! Self-delimiting binary lists with an executable inverse and exact bit length. -/
namespace HiddenCircuits.Complexity

def encodeBitList : List BitString → BitString
  | [] => []
  | x :: xs => true :: pairBits x (encodeBitList xs)

def decodeBitListFuel : ℕ → BitString → Option (List BitString)
  | 0, [] => some []
  | 0, _::_ => none
  | _+1, [] => some []
  | n+1, true::s =>
    match unpairBits s with
    | none => none
    | some (x,xs) => (decodeBitListFuel n xs).map (List.cons x)
  | _+1, false::_ => none

@[simp] theorem encodeBitList_length (xs : List BitString) :
    (encodeBitList xs).length = ((xs.map List.length).sum)*2 + xs.length*2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeBitList,ih]; omega

theorem list_length_le_encodeBitList_length (xs : List BitString) :
    xs.length ≤ (encodeBitList xs).length := by
  rw [encodeBitList_length]
  omega

theorem decodeBitListFuel_encode (xs : List BitString) (fuel : ℕ) (h : xs.length ≤ fuel) :
    decodeBitListFuel fuel (encodeBitList xs) = some xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons x xs ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      simp only [encodeBitList,decodeBitListFuel,unpair_pairBits]
      rw [ih fuel (by simpa using Nat.le_of_succ_le_succ h)]
      rfl

def decodeBitList (s : BitString) : Option (List BitString) := decodeBitListFuel s.length s

@[simp] theorem decodeBitList_encode (xs : List BitString) :
    decodeBitList (encodeBitList xs) = some xs :=
  decodeBitListFuel_encode xs _ (list_length_le_encodeBitList_length xs)

def bitListEncoding : Computability.FinEncoding (List BitString) where
  Γ := Bool
  ΓFin := inferInstance
  encode := encodeBitList
  decode := decodeBitList
  decode_encode := decodeBitList_encode

theorem encodeBitList_injective : Function.Injective encodeBitList := bitListEncoding.encode_injective

end HiddenCircuits.Complexity
