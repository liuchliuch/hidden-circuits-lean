import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! Actual finite signed-magnitude integer multiplication. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock

noncomputable def signedMultiplicationBlock : OracleBlock 5 := signedBinary multiplicationBlock 2

/-- The sign bits and magnitudes are all read and written by the actual finite
machine. Zero receives its unique nonnegative signed representation. -/
theorem signed_multiply_binary_output (g : BitString → ℕ) (a b : ℤ) :
    ∃ t : ℕ, signedMultiplicationBlock.Executes g
      (mulStore (signedBits a) (signedBits b) [] [] [] [])
      (mulStore [] (Computability.encodeNat b.natAbs) (signedBits (a*b)) [] [] []) t ∧
      t ≤ 13+2*(Computability.encodeNat a.natAbs).length+
        (Computability.encodeNat a.natAbs).length*
          (5*((Computability.encodeNat a.natAbs).length*((Computability.encodeNat b.natAbs).length+2))+
            10*(Computability.encodeNat b.natAbs).length+22) := by
  obtain ⟨t,ht,hbound⟩ := multiply_binary_output g a.natAbs b.natAbs
  have h := signedBinary_executes multiplicationBlock (2 : Fin 6) g ht (negative a) (negative b)
  have hs : withSigns (mulStore (Computability.encodeNat a.natAbs) (Computability.encodeNat b.natAbs) [] [] [] [])
      (negative a) (negative b) = mulStore (signedBits a) (signedBits b) [] [] [] [] := by
    funext i; fin_cases i <;> rfl
  have hr : Function.update (mulStore [] (Computability.encodeNat b.natAbs)
      (Computability.encodeNat (a.natAbs*b.natAbs)) [] [] []) (2 : Fin 6)
      (finishSigned (xor (negative a) (negative b)) (Computability.encodeNat (a.natAbs*b.natAbs))) =
      mulStore [] (Computability.encodeNat b.natAbs) (signedBits (a*b)) [] [] [] := by
    funext i; fin_cases i <;> first | rfl | exact finishSigned_mul a b
  change signedMultiplicationBlock.Executes g _
    (Function.update (mulStore [] (Computability.encodeNat b.natAbs)
      (Computability.encodeNat (a.natAbs*b.natAbs)) [] [] []) (2 : Fin 6)
      (finishSigned (xor (negative a) (negative b)) (Computability.encodeNat (a.natAbs*b.natAbs))))
    (t+finishCost (Computability.encodeNat (a.natAbs*b.natAbs))+6) at h
  rw [hs,hr] at h
  refine ⟨_,h,?_⟩
  have hf := finishCost_le (Computability.encodeNat (a.natAbs*b.natAbs))
  omega

theorem signedMultiplicationBlock_queryFree : signedMultiplicationBlock.QueryFree :=
  signedBinary_queryFree _ _ multiplicationBlock_queryFree

end HiddenCircuits.Complexity.BinaryArithmetic
