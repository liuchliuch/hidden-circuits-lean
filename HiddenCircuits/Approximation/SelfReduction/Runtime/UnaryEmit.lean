import HiddenCircuits.Complexity.OracleRepeat
import HiddenCircuits.Complexity.BitList

/-! Actual dynamic serialization of a unary value into a reversed list stream.
One final ordinary bit reversal yields the values in their original scan order. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock

theorem pairBits_unary (n : ℕ) (rest : BitString) :
    pairBits (List.replicate n true) rest = List.replicate (2*n) true ++ false::rest := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, pairBits, ih]
    rw [show 2*(n+1)=2+2*n by omega, List.replicate_add]
    rfl

 theorem repeated_pair_bits (n : ℕ) : (List.replicate n ([true,true] : BitString)).flatten = List.replicate (2*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, ih]
    rw [show 2*(n+1)=2+2*n by omega, List.replicate_add]
    rfl

noncomputable def emitUnaryReversed {k : ℕ} (counter output : Fin (k+1)) : OracleBlock k :=
  seq (push output true) (seq (repeatPrepend counter output [true,true]) (push output false))

/-- Exact linear-time dynamic serialization with complete frame preservation. -/
theorem emitUnaryReversed_executes {k : ℕ} (g : BitString → ℕ) (counter output : Fin (k+1))
    (hne : counter ≠ output) (s : Store k) :
    (emitUnaryReversed counter output).Executes g s
      (Function.update (Function.update s counter []) output
        ((true::pairBits (List.replicate (s counter).length true) []).reverse ++ s output))
      (9*(s counter).length+7) := by
  let s1 := Function.update s output (true::s output)
  have h1 : (push output true).Executes g s s1 1 := push_executes g output true s
  have h2 := repeatPrepend_executes g counter output hne [true,true] s1
  let s2 := Function.update (Function.update s counter []) output
    ((List.replicate (s counter).length [true,true]).flatten ++ true::s output)
  have h2' : (repeatPrepend counter output [true,true]).Executes g s1 s2 (9*(s counter).length+1) := by
    convert h2 using 1
    · simp only [s1, Function.update_of_ne hne]
      funext i
      by_cases hi : i=output
      · subst i; simp [s1,s2]
      · by_cases hj : i=counter
        · subst i; simp [s1,s2,hne]
        · simp [s1,s2,hi,hj]
    · simp [s1,hne]
  have h3 := push_executes g output false s2
  have h := seq_executes _ _ g h1 (seq_executes _ _ g h2' h3)
  convert h using 1
  · funext i
    by_cases hi : i=output
    · subst i
      simp [s2, pairBits_unary, repeated_pair_bits, List.reverse_cons, List.reverse_append,
        List.reverse_replicate, List.append_assoc]
    · simp [s2,hi]
  · omega

 theorem emitUnaryReversed_queryFree {k : ℕ} (counter output : Fin (k+1)) :
    (emitUnaryReversed counter output).QueryFree :=
  seq_queryFree _ _ (push_queryFree _ _) (seq_queryFree _ _ (repeatPrepend_queryFree _ _ _) (push_queryFree _ _))

end HiddenCircuits.Approximation.SelfReduction.Runtime
