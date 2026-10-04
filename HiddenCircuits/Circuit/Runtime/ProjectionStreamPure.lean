import HiddenCircuits.Circuit.Runtime.LetterEmitterFixed
import HiddenCircuits.GlobalProjectionWord
import HiddenCircuits.Complexity.BinaryArithmetic.WeightStreamsEmit

namespace HiddenCircuits.Circuit.Runtime.ProjectionStream
open HiddenCircuits.Complexity LetterEmitter

def filterStream (p : ℕ) : ℕ → BitString
  | 0 => []
  | n+1 => wordBitsAt p filterWord ++ filterStream (p+4) n

theorem wordBitsAt_left {a : ℕ} (b p : ℕ) (w : List (Letter a)) :
    wordBitsAt p (w.map (Letter.inLeft b))=wordBitsAt p w := by
  simp [wordBitsAt,List.flatMap_map,Function.comp_def,Letter.inLeft,leftIndex]

theorem wordBitsAt_right {b : ℕ} (a p : ℕ) (w : List (Letter b)) :
    wordBitsAt p (w.map (Letter.inRight a))=wordBitsAt (p+a) w := by
  simp [wordBitsAt,List.flatMap_map,Function.comp_def,Letter.inRight,rightIndex,Nat.add_assoc]

theorem filterStream_eq (p n : ℕ) : filterStream p n=wordBitsAt p (globalFilterWord n) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [filterStream,globalFilterWord,wordBitsAt,List.flatMap_append]
    change wordBitsAt p filterWord ++ filterStream (p+4) n=_
    rw [ih]
    rw [←wordBitsAt_left (blockWidth n) p filterWord,←wordBitsAt_right 4 p (globalFilterWord n)]
    rfl

theorem projectionStream_eq (n : ℕ) :
    (List.replicate (globalProjectionExponent n) (filterStream 0 n)).flatten=
      encodeBitList ((globalProjectionWord n).map letterBits) := by
  rw [filterStream_eq,wordBitsAt_zero]
  unfold globalProjectionWord
  induction globalProjectionExponent n with
  | zero => rfl
  | succ r ih =>
    simp only [List.replicate_succ,List.flatten_cons,List.map_append,
      BinaryArithmetic.encodeBitList_append,ih]
end HiddenCircuits.Circuit.Runtime.ProjectionStream
