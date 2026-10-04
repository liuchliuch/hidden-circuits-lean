import HiddenCircuits.Approximation.Initialization.TapeWords
import HiddenCircuits.Approximation.Initialization.TutteInteger

/-! Fixed-width emitted words are exactly the raw integer coordinates
whose finite uniform law was proved in TutteInteger. -/
namespace HiddenCircuits.Approximation.Initialization.TapeWords
open Complexity Complexity.BinaryArithmetic

theorem words_ofFn (B q : ℕ) (source : BitString) :
    words B q source = List.ofFn
      (fun i : Fin q => Computability.encodeNat (TutteInteger.number B source i.val)) := by
  induction q generalizing source with
  | zero => simp [words]
  | succ q ih =>
    rw [words,List.ofFn_succ,ih]
    congr 1
    · simp [word,TutteInteger.number]
    · apply congrArg List.ofFn
      funext i
      simp [TutteInteger.number,List.drop_drop,Nat.add_mul,Nat.add_comm]

theorem get_word (B q : ℕ) (source : BitString) (i : Fin q) :
    (words B q source)[i.val]?.getD [] =
      Computability.encodeNat (TutteInteger.number B source i.val) := by
  rw [words_ofFn]
  simp

end HiddenCircuits.Approximation.Initialization.TapeWords
