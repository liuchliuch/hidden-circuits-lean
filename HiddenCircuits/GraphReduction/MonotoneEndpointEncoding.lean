import HiddenCircuits.GraphReduction.MonotoneEndpointBridge
import HiddenCircuits.Complexity.BitList

/-! Canonical unary endpoint arrays for the restricted-permutation input.
The half-open convention [lo,hi) corresponds to one-based [lo+1,hi]. -/
namespace HiddenCircuits.GraphReduction
open Complexity Approximation
namespace MonotoneEndpointEncoding

abbrev Input := Σn : ℕ,MonotoneEndpoints n

def rows {n : ℕ} (f : Fin n → ℕ) : List BitString := List.ofFn (fun i => List.replicate (f i) true)
def encode (E : Input) : BitString :=
  encodeBitList [List.replicate E.1 true,encodeBitList (rows E.2.lo),encodeBitList (rows E.2.hi)]

def ofFunctions {n : ℕ} (lo hi : Fin n → ℕ) : Option (MonotoneEndpoints n) :=
  if h : Monotone lo ∧ Monotone hi ∧ (∀i,lo i ≤ hi i) ∧ (∀i,hi i ≤ n) then
    some ⟨lo,hi,h.1,h.2.1,h.2.2.1,h.2.2.2⟩ else none

@[simp] theorem ofFunctions_endpoints {n : ℕ} (E : MonotoneEndpoints n) :
    ofFunctions E.lo E.hi=some E := by
  unfold ofFunctions
  rw [dif_pos ⟨E.lo_mono,E.hi_mono,E.lo_le_hi,E.hi_le⟩]

def decodeRows (n : ℕ) (xs : List BitString) : Option (Fin n → ℕ) :=
  if hl : xs.length=n then
    if h : ∀i : Fin n,xs.get (Fin.cast hl.symm i)=List.replicate (xs.get (Fin.cast hl.symm i)).length true then
      some (fun i => (xs.get (Fin.cast hl.symm i)).length) else none
  else none

@[simp] theorem decodeRows_rows {n : ℕ} (f : Fin n → ℕ) : decodeRows n (rows f)=some f := by
  unfold decodeRows
  rw [dif_pos (by simp [rows])]
  simp [rows,List.get_eq_getElem]

def decodePayload (n : ℕ) (ls hs : BitString) : Option Input :=
  match decodeBitList ls,decodeBitList hs with
  | some lows,some highs =>
    match decodeRows n lows,decodeRows n highs with
    | some lo,some hi => (ofFunctions lo hi).map (fun E => ⟨n,E⟩)
    | _,_ => none
  | _,_ => none

@[simp] theorem decodePayload_rows {n : ℕ} (E : MonotoneEndpoints n) :
    decodePayload n (encodeBitList (rows E.lo)) (encodeBitList (rows E.hi))=some ⟨n,E⟩ := by
  simp [decodePayload]

def decode (xs : BitString) : Option Input :=
  match decodeBitList xs with
  | some [header,ls,hs] =>
    if header=List.replicate header.length true then decodePayload header.length ls hs else none
  | _ => none

@[simp] theorem decode_encode (E : Input) : decode (encode E)=some E := by
  rcases E with ⟨n,E⟩
  simp [decode,encode]

def encoding : Computability.FinEncoding Input where
  Γ := Bool
  ΓFin := inferInstance
  encode := encode
  decode := decode
  decode_encode := decode_encode

theorem encode_injective : Function.Injective encode := encoding.encode_injective

theorem rows_length {n : ℕ} (f : Fin n → ℕ) : (rows f).length=n := by simp [rows]
theorem rows_size {n : ℕ} (f : Fin n → ℕ) (hf : ∀i,f i ≤ n) :
    ((rows f).map List.length).sum ≤ n*n := by
  simp only [rows,List.map_ofFn,List.sum_ofFn,Function.comp_apply,List.length_replicate]
  calc
    ∑i : Fin n,f i ≤ ∑_i : Fin n,n := Finset.sum_le_sum (fun i _ => hf i)
    _ = _ := by simp

theorem encode_length (E : Input) : (encode E).length ≤ 8*E.1^2+10*E.1+6 := by
  have hlo := rows_size E.2.lo (fun i => (E.2.lo_le_hi i).trans (E.2.hi_le i))
  have hhi := rows_size E.2.hi E.2.hi_le
  simp only [encode,encodeBitList_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil,List.length_replicate,rows_length]
  nlinarith

noncomputable def count (xs : BitString) : ℕ :=
  match decode xs with
  | none => 0
  | some E => Fintype.card E.2.Permutations
@[simp] theorem count_encode (E : Input) : count (encode E)=Fintype.card E.2.Permutations := by simp [count]
end MonotoneEndpointEncoding
end HiddenCircuits.GraphReduction
