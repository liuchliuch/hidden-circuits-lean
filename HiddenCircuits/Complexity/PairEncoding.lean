import HiddenCircuits.GraphReduction.Runtime.WordGraph.PairEncoding
import HiddenCircuits.PairedLayerGraph
import HiddenCircuits.Complexity.RecoveryBitBounds
import HiddenCircuits.Complexity.BinaryArithmetic.AccumulatorBounds

/-! Canonical standalone PairEval instances: positive width, both boundary
masks, and a nonempty explicit sequence of the five permitted cut pairs. -/
namespace HiddenCircuits.Complexity
open GraphReduction.Runtime GraphReduction.Runtime.WordGraph BinaryArithmetic

structure PairInput where
  particles : ℕ
  positive : 0 < particles
  source : State (2*particles) particles
  target : State (2*particles) particles
  pairs : List (CutPair particles)
  nonempty : pairs ≠ []

def pairInputBits (w : PairInput) : BitString :=
  pairBits (List.replicate w.particles true)
    (encodeBitList (stateBits w.source :: stateBits w.target :: w.pairs.map pairAtom))

def decodePairIndex (p : ℕ) (xs : BitString) : Option (Fin (2*p-1)) :=
  if h : xs.length < 2*p-1 then
    if xs = List.replicate xs.length true then some ⟨xs.length,h⟩ else none
  else none

def decodePairAtom (p : ℕ) : BitString → Option (CutPair p)
  | [false,false,false,false] => some .background
  | true::false::false::false::xs => (decodePairIndex p xs).map CutPair.leftRise
  | false::true::false::false::xs => (decodePairIndex p xs).map CutPair.leftDrop
  | false::false::true::false::xs => (decodePairIndex p xs).map CutPair.rightRise
  | false::false::false::true::xs => (decodePairIndex p xs).map CutPair.rightDrop
  | _ => none

@[simp] lemma decodePairIndex_encode {p : ℕ} (i : Fin (2*p-1)) :
    decodePairIndex p (List.replicate i.val true)=some i := by
  simp [decodePairIndex,i.isLt]
@[simp] lemma decodePairAtom_pairAtom {p : ℕ} (P : CutPair p) :
    decodePairAtom p (pairAtom P)=some P := by
  cases P <;> simp [pairAtom,pairTag,cutCode,decodePairAtom]

def decodePairs (p : ℕ) : List BitString → Option (List (CutPair p))
  | [] => some []
  | x::xs => match decodePairAtom p x, decodePairs p xs with
    | some P,some ps => some (P::ps)
    | _,_ => none
@[simp] lemma decodePairs_encode {p : ℕ} (ps : List (CutPair p)) :
    decodePairs p (ps.map pairAtom)=some ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [decodePairs,ih]

def decodePairPayload (p : ℕ) (hp : 0<p) (payload : BitString) : Option PairInput :=
  match decodeBitList payload with
  | some (source::target::atoms) =>
    match decodeState (2*p) p source, decodeState (2*p) p target, decodePairs p atoms with
    | some S,some T,some ps => if h : ps≠[] then some ⟨p,hp,S,T,ps,h⟩ else none
    | _,_,_ => none
  | _ => none

def decodePairInput (xs : BitString) : Option PairInput :=
  match unpairBits xs with
  | none => none
  | some (header,payload) =>
    if hp : 0<header.length then
      if header=List.replicate header.length true then decodePairPayload header.length hp payload else none
    else none

@[simp] theorem decodePairInput_pairInputBits (w : PairInput) :
    decodePairInput (pairInputBits w)=some w := by
  rcases w with ⟨p,hp,S,T,ps,hps⟩
  simp only [decodePairInput,pairInputBits,unpair_pairBits,List.length_replicate]
  simp [hp,decodePairPayload,hps,List.length_replicate]

def pairInputEncoding : Computability.FinEncoding PairInput where
  Γ := Bool
  ΓFin := inferInstance
  encode := pairInputBits
  decode := decodePairInput
  decode_encode := decodePairInput_pairInputBits

theorem pairInputBits_injective : Function.Injective pairInputBits := pairInputEncoding.encode_injective

noncomputable def PairInput.value (w : PairInput) : ℕ :=
  Layered.matchingCount (pairCuts w.pairs) w.source w.target

lemma PairInput.value_eq_matrix (w : PairInput) :
    (w.value:ℚ)=pairWordMatrix w.pairs w.source w.target :=
  (pairWordMatrix_eq_matchingCount _ _ _).symm

noncomputable def pairEval (xs : BitString) : ℕ :=
  match decodePairInput xs with
  | none => 0
  | some w => w.value

@[simp] theorem pairEval_pairInputBits (w : PairInput) : pairEval (pairInputBits w)=w.value := by
  simp [pairEval]
lemma pairEval_malformed (xs : BitString) (h : decodePairInput xs=none) : pairEval xs=0 := by
  simp [pairEval,h]

lemma pairInputBits_length (w : PairInput) :
    (pairInputBits w).length=10*w.particles+(pairStream w.pairs).length+5 := by
  simp only [pairInputBits,pairBits_length,List.length_replicate,encodeBitList,List.length_cons,
    stateBits_length,pairStream]
  omega
lemma pairInputBits_length_lower (w : PairInput) :
    w.particles+w.pairs.length+1≤(pairInputBits w).length := by
  rw [pairInputBits_length]
  have hp : w.pairs.length≤(pairStream w.pairs).length := by
    simp only [pairStream,encodeBitList_length,List.length_map]
    omega
  omega
lemma pairInputBits_length_upper (w : PairInput) :
    (pairInputBits w).length≤10*w.particles+w.pairs.length*(10+4*w.particles)+5 := by
  rw [pairInputBits_length]
  exact Nat.add_le_add_right (Nat.add_le_add_left (pairStream_length_bound w.pairs) _) _

lemma PairInput.value_bound (w : PairInput) :
    w.value≤2^((4*w.particles*w.pairs.length)^2) := by
  have h := perfectMatchingCount_bound (Layered.retainedGraph (pairCuts w.pairs) w.source w.target)
  rw [pairCuts_vertex_count _ w.nonempty] at h
  calc
    w.value≤(4*w.particles*w.pairs.length+1)^(4*w.particles*w.pairs.length) := h
    _≤(2^(4*w.particles*w.pairs.length))^(4*w.particles*w.pairs.length) :=
      Nat.pow_le_pow_left (succ_le_two_pow _) _
    _=2^((4*w.particles*w.pairs.length)^2) := by rw [←pow_mul,pow_two]

lemma PairInput.output_length (w : PairInput) :
    (Computability.encodeNat w.value).length≤16*(pairInputBits w).length^4+1 := by
  have hn:=pairInputBits_length_lower w
  have hp : w.particles≤(pairInputBits w).length := by omega
  have hh : w.pairs.length≤(pairInputBits w).length := by omega
  have hmul : 4*w.particles*w.pairs.length≤4*(pairInputBits w).length^2 := by nlinarith [Nat.mul_le_mul hp hh]
  have he : (4*w.particles*w.pairs.length)^2≤16*(pairInputBits w).length^4 := by nlinarith [Nat.pow_le_pow_left hmul 2]
  have hs:=signedBits_length_of_abs_bound (z:=(w.value:ℤ)) (by simpa using w.value_bound)
  simp only [signedBits,List.length_cons,Int.natAbs_natCast] at hs
  omega
end HiddenCircuits.Complexity
