import HiddenCircuits.DH.Runtime.NumericStateModel
import HiddenCircuits.DH.Runtime.PairCheckModel
import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! Canonical nested word arrays for the actual finite-stack counter. -/
namespace HiddenCircuits.DH.Runtime.NumericEncoding
open Complexity Complexity.BinaryArithmetic NumericStateModel

 def words (row : List ℕ) : List BitString := row.map (fun (z : ℕ)=>signedBits (z:ℤ))
 def rowBits (row : List ℕ) : BitString := encodeBitList (words row)
 def tableWords {n : ℕ} (s : NumericStateModel.State n) : List BitString := s.rows.toList.map rowBits
 def tableBits {n : ℕ} (s : NumericStateModel.State n) : BitString := encodeBitList (tableWords s)
 def sizeWords {n : ℕ} (s : NumericStateModel.State n) : List BitString := s.sizes.toList.map (fun z=>List.replicate z true)
 def sizeBits {n : ℕ} (s : NumericStateModel.State n) : BitString := encodeBitList (sizeWords s)

@[simp] lemma positive_word (z : ℕ) : signedBits (z:ℤ)=false::Computability.encodeNat z := by
  simp [signedBits,negative]

@[simp] lemma zero_word : signedBits (0:ℤ)=[false] := rfl
@[simp] lemma one_word : signedBits (1:ℤ)=[false,true] := rfl

lemma leafRow_set (n : ℕ) : CoefficientModel.leafRow n=(List.replicate (n+1) 0).set 1 1 := by
  apply List.ext_getElem
  · simp [CoefficientModel.leafRow]
  · intro i hi hi'
    simp only [CoefficientModel.leafRow,List.getElem_ofFn,List.getElem_set]
    by_cases he : i=1
    · subst i;simp
    · have hrev : ¬1=i := Ne.symm he
      simp [he,hrev]

lemma leaf_words (n : ℕ) : words (CoefficientModel.leafRow n)=
    (List.replicate (n+1) [false]).set 1 [false,true] := by
  rw [leafRow_set]
  simp only [words,List.map_set,List.map_replicate,Nat.cast_zero,Nat.cast_one,zero_word,one_word]

lemma tableWords_get {n : ℕ} (s : NumericStateModel.State n) (v : Fin n) :
    (tableWords s)[v.val]?.getD []=rowBits s.rows[v.val] := by
  simp [tableWords,List.getElem?_eq_getElem,v.isLt]

lemma sizeWords_get {n : ℕ} (s : NumericStateModel.State n) (v : Fin n) :
    (sizeWords s)[v.val]?.getD []=List.replicate s.sizes[v.val] true := by
  simp [sizeWords,List.getElem?_eq_getElem,v.isLt]

lemma rowWords_get (row : List ℕ) (k : ℕ) (hk : k<row.length) :
    (words row)[k]?.getD []=signedBits (CoefficientModel.read row k:ℤ) := by
  simp [words,CoefficientModel.read,List.getElem?_eq_getElem,hk]

lemma initial_table (n : ℕ) : tableBits (initial n)=
    encodeBitList (List.replicate n (encodeBitList ((List.replicate (n+1) [false]).set 1 [false,true]))) := by
  simp [tableBits,tableWords,initial,rowBits,leaf_words]

lemma initial_sizes (n : ℕ) : sizeBits (initial n)=encodeBitList (List.replicate n [true]) := by
  simp [sizeBits,sizeWords,initial]

lemma initial_alive (n : ℕ) : PairCheck.liveBits (initial n).alive=encodeBitList (List.replicate n [true]) := by
  simp [PairCheck.liveBits,PairCheck.liveWords,initial]

lemma positive_word_bound {z B : ℕ} (h : z≤2^B) : (signedBits (z:ℤ)).length≤B+2 := by
  have hb := Nat.size_le_size h
  rw [Nat.size_pow] at hb
  simp only [positive_word,List.length_cons,encodeNat_length]
  omega

lemma sum_length_le (ws : List BitString) (B : ℕ) (h : ∀w∈ws, w.length≤B) :
    (ws.map List.length).sum≤ws.length*B := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw := h w List.mem_cons_self
    have ht := ih (fun x hx=>h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma rowBits_bound (row : List ℕ) (n B : ℕ) (hlen : row.length=n+1)
    (h : ∀k, CoefficientModel.read row k≤2^B) :
    (rowBits row).length≤2*(n+1)*(B+3) := by
  have hw : ∀w∈words row, w.length≤B+2 := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hw
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hz
    have hh := h i
    have hread : CoefficientModel.read row i=z := by simp [CoefficientModel.read,List.getElem?_eq_getElem,hi,he]
    rw [hread] at hh
    exact positive_word_bound hh
  have hs := sum_length_le (words row) (B+2) hw
  simp only [words,List.length_map,hlen] at hs
  simp only [rowBits,encodeBitList_length,words,List.length_map,hlen]
  change (List.map List.length (words row)).sum*2+(n+1)*2≤_
  change (List.map List.length (words row)).sum≤(n+1)*(B+2) at hs
  nlinarith

end HiddenCircuits.DH.Runtime.NumericEncoding
