import HiddenCircuits.Complexity.BitList
import HiddenCircuits.BitBounds

/-! Actual finite WordEval inputs have a canonical binary representation. -/
namespace HiddenCircuits.Complexity
open HiddenCircuits

/-- Explicit subset mask, in increasing track order. -/
def stateBits {n q : ℕ} (S : State n q) : BitString :=
  List.ofFn (fun i : Fin n => decide (i ∈ S.val))

@[simp] theorem stateBits_length {n q : ℕ} (S : State n q) : (stateBits S).length = n := by
  simp [stateBits]

def decodeState (n q : ℕ) (s : BitString) : Option (State n q) :=
  if h : s.length = n then
    let S := Finset.univ.filter (fun i : Fin n => s.get ⟨i.val,by simpa [h] using i.isLt⟩ = true)
    if hc : S.card = q then some ⟨S,hc⟩ else none
  else none

lemma stateBits_get {n q : ℕ} (S : State n q) (i : Fin n)
    (h : i.val < (stateBits S).length) :
    (stateBits S).get ⟨i.val,h⟩ = decide (i ∈ S.val) := by
  simp only [stateBits,List.get_ofFn]
  rfl

@[simp] theorem decodeState_stateBits {n q : ℕ} (S : State n q) :
    decodeState n q (stateBits S) = some S := by
  unfold decodeState
  simp only [stateBits_length,dite_true,stateBits_get,decide_eq_true_eq]
  have hset : (Finset.univ.filter (fun i : Fin n => i ∈ S.val)) = S.val := by ext i; simp
  simp only [hset,S.property,dite_true]
  rfl

def kindBits : LetterKind → BitString
  | .R => [false,false]
  | .D => [false,true]
  | .B => [true,false]
  | .E => [true,true]

def decodeKind : BitString → Option LetterKind
  | [false,false] => some .R
  | [false,true] => some .D
  | [true,false] => some .B
  | [true,true] => some .E
  | _ => none

@[simp] theorem decodeKind_kindBits (k : LetterKind) : decodeKind (kindBits k) = some k := by
  cases k <;> rfl

@[simp] theorem kindBits_length (k : LetterKind) : (kindBits k).length = 2 := by
  cases k <;> rfl

def letterBits {n : ℕ} (l : Letter n) : BitString :=
  pairBits (kindBits l.kind) (List.replicate l.index.val true)

def decodeLetter (n : ℕ) (s : BitString) : Option (Letter n) :=
  match unpairBits s with
  | none => none
  | some (kb,ib) =>
    match decodeKind kb with
    | none => none
    | some k =>
      if h : ib.length < n-1 then
        if ib = List.replicate ib.length true then some ⟨k,⟨ib.length,h⟩⟩ else none
      else none

@[simp] theorem letterBits_length {n : ℕ} (l : Letter n) :
    (letterBits l).length = l.index.val+5 := by simp [letterBits]; omega

@[simp] theorem decodeLetter_letterBits {n : ℕ} (l : Letter n) :
    decodeLetter n (letterBits l) = some l := by
  rcases l with ⟨k,i⟩
  simp [decodeLetter,letterBits,i.isLt]

/-- The payload lists source mask, target mask, and all letters in exact order. -/
def wordBits (w : WordInstance) : BitString :=
  pairBits (List.replicate w.particles true)
    (encodeBitList (stateBits w.source :: stateBits w.target :: w.word.map letterBits))

/-- Decode a list of letters without changing order or allowing malformed atoms. -/
def decodeLetters (n : ℕ) : List BitString → Option (List (Letter n))
  | [] => some []
  | s::ss =>
    match decodeLetter n s, decodeLetters n ss with
    | some l, some ls => some (l::ls)
    | _,_ => none

@[simp] theorem decodeLetters_letterBits {n : ℕ} (ls : List (Letter n)) :
    decodeLetters n (ls.map letterBits) = some ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [decodeLetters,ih]

def decodeWordPayload (p : ℕ) (hp : 0 < p) (payload : BitString) : Option WordInstance :=
  match decodeBitList payload with
  | some (source::target::letters) =>
    match decodeState (2*p) p source, decodeState (2*p) p target, decodeLetters (2*p) letters with
    | some S,some T,some w => some ⟨p,hp,S,T,w⟩
    | _,_,_ => none
  | _ => none

@[simp] theorem decodeWordPayload_encode (p : ℕ) (hp : 0 < p)
    (S T : State (2*p) p) (w : List (Letter (2*p))) :
    decodeWordPayload p hp (encodeBitList (stateBits S :: stateBits T :: w.map letterBits)) =
      some ⟨p,hp,S,T,w⟩ := by
  simp [decodeWordPayload]

/-- Parse all components and check positivity, cardinalities, and index ranges. -/
def decodeWord (s : BitString) : Option WordInstance :=
  match unpairBits s with
  | none => none
  | some (header,payload) =>
    if hpos : 0 < header.length then
      if header = List.replicate header.length true then
        decodeWordPayload header.length hpos payload
      else none
    else none

@[simp] theorem decodeWord_wordBits (w : WordInstance) : decodeWord (wordBits w) = some w := by
  rcases w with ⟨p,hp,S,T,w⟩
  simp [decodeWord,wordBits,hp]

/-- An executable binary encoding with a proved inverse, including all boundary states. -/
def wordEncoding : Computability.FinEncoding WordInstance where
  Γ := Bool
  ΓFin := inferInstance
  encode := wordBits
  decode := decodeWord
  decode_encode := decodeWord_wordBits

theorem wordBits_injective : Function.Injective wordBits := wordEncoding.encode_injective

/-- Exact binary length, exposing all subset masks and letter atoms. -/
theorem wordBits_length (w : WordInstance) :
    (wordBits w).length = 10*w.particles +
      2*(w.word.map (fun l => (letterBits l).length)).sum + 2*w.word.length + 5 := by
  simp only [wordBits,pairBits_length,List.length_replicate,encodeBitList_length,
    List.map_cons,stateBits_length,List.sum_cons,List.length_cons,List.length_map,
    List.map_map,Function.comp_def]
  omega

theorem wordBits_length_lower (w : WordInstance) :
    2*w.particles+w.word.length+1 ≤ (wordBits w).length := by
  rw [wordBits_length]
  omega

/-- The arithmetic WordEval bit bound is now a bound in the actual input bits. -/
theorem word_value_bits_input (w : WordInstance) :
    ∃ z : ℤ, w.value = (z : ℚ) ∧ z.natAbs.size+1 ≤ 14*(wordBits w).length^5 := by
  obtain ⟨z,hz,hb⟩ := w.value_bit_bound_tracks
  refine ⟨z,hz,hb.trans ?_⟩
  exact Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left (wordBits_length_lower w) 5)

end HiddenCircuits.Complexity
