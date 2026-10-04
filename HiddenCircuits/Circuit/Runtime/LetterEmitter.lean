import HiddenCircuits.Complexity.WordEncoding
import HiddenCircuits.Complexity.CNFSerialization
import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.Complexity.OracleStream
import HiddenCircuits.Complexity.GraphVerifier.DropClock

/-! Actual finite serialization of any of the four elementary letter kinds from a
preserved unary physical index. Every nested paired-list delimiter is emitted. -/
namespace HiddenCircuits.Circuit.Runtime.LetterEmitter
open HiddenCircuits.Complexity OracleBlock

def atomPrefix (tag : LetterKind) : BitString := true :: (escapeBits (escapeBits (kindBits tag)) ++ [true,false])
def chunk (tag : LetterKind) (position : ℕ) : BitString :=
  atomPrefix tag ++ List.replicate (2*position) true ++ [false]

lemma atomPrefix_length (tag : LetterKind) : (atomPrefix tag).length=11 := by cases tag <;> rfl

lemma chunk_eq (tag : LetterKind) (position : ℕ) :
    chunk tag position=encodeBitList [pairBits (kindBits tag) (List.replicate position true)] := by
  simp [chunk,atomPrefix,encodeBitList,pairBits_escape,escapeBits_append,escapeBits,escapeBits_replicate_true,List.append_assoc]

lemma chunk_gate {n : ℕ} (g : Letter n) :
    chunk (g.kind) (g.index.val)=encodeBitList [letterBits g] := chunk_eq _ _

lemma chunks_eq {n : ℕ} (gs : List (Letter n)) :
    gs.flatMap (fun g => chunk (g.kind) (g.index.val))=encodeBitList (gs.map letterBits) := by
  simp only [chunk_gate,encodeBitList_eq_flatMap,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.flatMap_map,Function.comp_def]

def store (position : ℕ) (stream counter temporary : BitString) : Store 3 := fun i =>
  if i.val=0 then List.replicate position true else if i.val=1 then stream else if i.val=2 then counter else temporary

noncomputable def atom (tag : LetterKind) : OracleBlock 3 :=
  seq (copyOn 0 2 3 (by decide) (by decide) (by decide))
    (seq (prepend 1 (atomPrefix tag).reverse) (seq (repeatPrepend 2 1 [true,true]) (push 1 false)))

theorem atom_executes (g : BitString → ℕ) (tag : LetterKind) (p : ℕ) (stream : BitString) :
    (atom tag).Executes g (store p stream [] [])
      (store p ((chunk tag p).reverse++stream) [] []) (14*p+44) := by
  have hcopy : (copyOn (0:Fin 4) 2 3 (by decide) (by decide) (by decide)).Executes g
      (store p stream [] []) (store p stream (List.replicate p true) []) (5*p+2) := by
    convert copyOn_executes g (0:Fin 4) 2 3 (by decide) (by decide) (by decide) (store p stream [] []) rfl using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [store]
  have hpre : (prepend (1:Fin 4) (atomPrefix tag).reverse).Executes g
      (store p stream (List.replicate p true) [])
      (store p ((atomPrefix tag).reverse++stream) (List.replicate p true) []) 34 := by
    convert prepend_executes g (1:Fin 4) (atomPrefix tag).reverse (store p stream (List.replicate p true) []) using 1
    · funext i;fin_cases i <;> simp [store]
    · simp [atomPrefix_length]
  have hrep : (repeatPrepend (2:Fin 4) 1 [true,true]).Executes g
      (store p ((atomPrefix tag).reverse++stream) (List.replicate p true) [])
      (store p (List.replicate (2*p) true++(atomPrefix tag).reverse++stream) [] []) (9*p+1) := by
    have he : (List.replicate p [true,true]).flatten=List.replicate (2*p) true := by
      change (List.replicate p (List.replicate 2 true)).flatten=List.replicate (2*p) true
      simp only [List.flatten_replicate_replicate,Nat.mul_comm]
    convert repeatPrepend_executes g (2:Fin 4) 1 (by decide) [true,true]
      (store p ((atomPrefix tag).reverse++stream) (List.replicate p true) []) using 1
    · funext i;fin_cases i <;> simp [store,he,List.append_assoc]
    · simp [store]
  have hlast : (push (1:Fin 4) false).Executes g
      (store p (List.replicate (2*p) true++(atomPrefix tag).reverse++stream) [] [])
      (store p ((chunk tag p).reverse++stream) [] []) 1 := by
    convert push_executes g (1:Fin 4) false (store p (List.replicate (2*p) true++(atomPrefix tag).reverse++stream) [] []) using 1
    funext i;fin_cases i <;> simp [store,chunk,List.reverse_append,List.append_assoc]
  convert seq_executes _ _ g hcopy (seq_executes _ _ g hpre (seq_executes _ _ g hrep hlast)) using 1 <;> omega

lemma atom_queryFree (tag : LetterKind) : (atom tag).QueryFree := seq_queryFree _ _ (copyOn_queryFree _ _ _ _ _ _)
  (seq_queryFree _ _ (prepend_queryFree _ _) (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (push_queryFree _ _)))


end HiddenCircuits.Circuit.Runtime.LetterEmitter
