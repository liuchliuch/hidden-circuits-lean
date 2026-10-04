import HiddenCircuits.Complexity.DeterminantRuntime.Negation
import HiddenCircuits.Complexity.BinaryArithmetic.UnaryBinary
import HiddenCircuits.Complexity.BinaryArithmetic.CleanOperations

/-! Literal conversion of a preserved unary round counter to its binary divisor. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime.Coefficient
open OracleBlock BinaryArithmetic

def state (k : ℕ) (trace result clock denominator : BitString) : Store 12 := fun q =>
  if q.val=0 then List.replicate k true else if q.val=1 then trace else
  if q.val=2 then result else if q.val=3 then clock else if q.val=4 then denominator else []
def store (k : ℕ) (trace result : BitString) : Store 12 := state k trace result [] []

def binaryPorts : Fin 3 ↪ Fin 13 where
  toFun := ![3,4,5]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
def divisionPorts : Fin 9 ↪ Fin 13 where
  toFun := ![2,4,3,5,6,7,8,9,10]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

noncomputable def denominatorProgram : OracleBlock 12 := seq
  (copyOn 0 3 5 (by decide) (by decide) (by decide))
  (seq (push 3 true) (seq (rename unaryBinary binaryPorts) (push 4 false)))

theorem denominator_executes (g : BitString → ℕ) (k : ℕ) (trace : BitString) :
    ∃ t, denominatorProgram.Executes g (store k trace [])
      (state k trace [] [] (signedBits ((k+1 : ℕ) : ℤ))) t ∧
      t ≤ 5*k+(k+1)*(4*(k+1)+5)+11 := by
  have h1 : (copyOn (0 : Fin 13) 3 5 (by decide) (by decide) (by decide)).Executes g
      (store k trace []) (state k trace [] (List.replicate k true) []) (5*k+2) := by
    have h := copyOn_executes g (0 : Fin 13) 3 5 (by decide) (by decide) (by decide) (store k trace []) rfl
    have he : Function.update (store k trace []) 3 (List.replicate k true) =
        state k trace [] (List.replicate k true) [] := by funext q; fin_cases q <;> rfl
    simpa only [show store k trace [] 0 = List.replicate k true from rfl,
      show store k trace [] 3 = [] from rfl,List.append_nil,List.length_replicate,he] using h
  have h2 : (push (3 : Fin 13) true).Executes g (state k trace [] (List.replicate k true) [])
      (state k trace [] (List.replicate (k+1) true) []) 1 := by
    convert push_executes g (3 : Fin 13) true (state k trace [] (List.replicate k true) []) using 1
    funext q; fin_cases q <;> rfl
  have h3 : (rename unaryBinary binaryPorts).Executes g (state k trace [] (List.replicate (k+1) true) [])
      (state k trace [] [] (Computability.encodeNat (k+1))) (unaryBinaryCost 0 (k+1)) := by
    have h := unaryBinary_executes g (List.replicate (k+1) true) 0
    simp only [List.length_replicate,Nat.zero_add] at h
    apply rename_executes_to unaryBinary binaryPorts g h
    · funext q; fin_cases q <;> rfl
    · funext q; fin_cases q <;> rfl
    · intro q hq; fin_cases q <;> first | exact (hq 0 rfl).elim | exact (hq 1 rfl).elim | rfl
  have h4 : (push (4 : Fin 13) false).Executes g (state k trace [] [] (Computability.encodeNat (k+1)))
      (state k trace [] [] (signedBits ((k+1 : ℕ) : ℤ))) 1 := by
    have he : signedBits ((k+1 : ℕ) : ℤ) = false::Computability.encodeNat (k+1) := by
      unfold signedBits
      rw [Int.natAbs_natCast]
      congr 1
    rw [he]
    convert push_executes g (4 : Fin 13) false (state k trace [] [] (Computability.encodeNat (k+1))) using 1
    funext q; fin_cases q <;> rfl
  refine ⟨_,seq_executes _ _ g h1 (seq_executes _ _ g h2 (seq_executes _ _ g h3 h4)),?_⟩
  have h := unaryBinaryCost_le (k+1) 0 (k+1) (by omega)
  omega

theorem denominatorProgram_queryFree : denominatorProgram.QueryFree := seq_queryFree _ _
  (copyOn_queryFree _ _ _ _ _ _) (seq_queryFree _ _ (push_queryFree _ _)
    (seq_queryFree _ _ (rename_queryFree _ _ unaryBinary_queryFree) (push_queryFree _ _)))

end HiddenCircuits.Complexity.DeterminantRuntime.Coefficient
