import HiddenCircuits.GraphReduction.Runtime.DescriptorAtomPure
import HiddenCircuits.Complexity.WordEncoding

namespace HiddenCircuits.GraphReduction.Runtime.WordGraph
open Complexity BinaryArithmetic

def pairTag {p : ℕ} (P : CutPair p) : BitString :=
  [(cutCode P).leftRise,(cutCode P).leftDrop,(cutCode P).rightRise,(cutCode P).rightDrop]
def pairAtom {p : ℕ} (P : CutPair p) : BitString := pairTag P ++ List.replicate (cutCode P).index true
def pairStream {p : ℕ} (ps : List (CutPair p)) : BitString := encodeBitList (ps.map pairAtom)
@[simp] theorem pairAtom_length {p : ℕ} (P : CutPair p) : (pairAtom P).length=4+(cutCode P).index := by simp [pairAtom,pairTag];omega
@[simp] theorem pairStream_nil (p : ℕ) : pairStream ([] : List (CutPair p))=[] := rfl
 theorem pairStream_append {p : ℕ} (ps qs : List (CutPair p)) : pairStream (ps++qs)=pairStream ps++pairStream qs := by
  simp only [pairStream,List.map_append,encodeBitList_append]
 theorem pairStream_cons {p : ℕ} (P : CutPair p) (ps : List (CutPair p)) : pairStream (P::ps)=wordChunk (pairAtom P)++pairStream ps := by
  simp only [pairStream,List.map_cons,encodeBitList_eq_chunks,List.flatMap_cons]
 theorem pairStream_replicate {p : ℕ} (n : ℕ) (P : CutPair p) :
    pairStream (List.replicate n P)=(List.replicate n (wordChunk (pairAtom P))).flatten := by
  simp [pairStream,encodeBitList_eq_chunks,List.flatMap]
 theorem pairStream_length_bound {p : ℕ} (ps : List (CutPair p)) : (pairStream ps).length≤ps.length*(10+4*p) := by
  induction ps with
  | nil => simp
  | cons P ps ih =>
    rw [pairStream_cons,List.length_append]
    have hp := cutCode_index_le P
    simp only [wordChunk,List.length_cons,pairBits_length,List.length_nil,pairAtom_length,List.length_cons]
    nlinarith
end HiddenCircuits.GraphReduction.Runtime.WordGraph
