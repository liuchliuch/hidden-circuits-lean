import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits
import HiddenCircuits.Complexity.BinaryArithmetic.Division

/-! Finite signed exact division for the integer interpolation accumulators. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic
open OracleBlock

noncomputable def signedDivisionBlock : OracleBlock 8 := signedBinary divisionBlock 3

/-- Exact signed division agrees with Lean's integer quotient. The divisor is
nonzero; exact divisibility is established by the calling algebraic algorithm. -/
theorem signed_exact_divide_binary_output (g : BitString → ℕ) (a b : ℤ) (hb : b≠0) (hdiv : b ∣ a) :
    ∃ t : ℕ, signedDivisionBlock.Executes g
      (divStore (signedBits a) (signedBits b) [] [] [] [] [] [] [])
      (divStore [] (Computability.encodeNat b.natAbs) [] (signedBits (a/b)) [] [] [] [] []) t ∧
      t ≤ (Computability.encodeNat a.natAbs).length*(25*(Computability.encodeNat b.natAbs).length+54)+13 := by
  have hn : 0<b.natAbs := Int.natAbs_pos.mpr hb
  have hd : b.natAbs ∣ a.natAbs := Int.natAbs_dvd_natAbs.mpr hdiv
  obtain ⟨t,ht,hbound⟩ := exact_divide_binary_output g a.natAbs b.natAbs hn hd
  have h := signedBinary_executes divisionBlock (3 : Fin 9) g ht (negative a) (negative b)
  have hs : withSigns
      (divStore (Computability.encodeNat a.natAbs) (Computability.encodeNat b.natAbs) [] [] [] [] [] [] [])
      (negative a) (negative b) = divStore (signedBits a) (signedBits b) [] [] [] [] [] [] [] := by
    funext i; fin_cases i <;> rfl
  have hr : Function.update (divStore [] (Computability.encodeNat b.natAbs) []
      (Computability.encodeNat (a.natAbs/b.natAbs)) [] [] [] [] []) (3 : Fin 9)
      (finishSigned (xor (negative a) (negative b)) (Computability.encodeNat (a.natAbs/b.natAbs))) =
      divStore [] (Computability.encodeNat b.natAbs) [] (signedBits (a/b)) [] [] [] [] [] := by
    funext i; fin_cases i <;> first | rfl | exact finishSigned_exact_div a b hb hdiv
  change signedDivisionBlock.Executes g _
    (Function.update (divStore [] (Computability.encodeNat b.natAbs) []
      (Computability.encodeNat (a.natAbs/b.natAbs)) [] [] [] [] []) (3 : Fin 9)
      (finishSigned (xor (negative a) (negative b)) (Computability.encodeNat (a.natAbs/b.natAbs))))
    (t+finishCost (Computability.encodeNat (a.natAbs/b.natAbs))+6) at h
  rw [hs,hr] at h
  refine ⟨_,h,?_⟩
  have hf := finishCost_le (Computability.encodeNat (a.natAbs/b.natAbs))
  omega

theorem signedDivisionBlock_queryFree : signedDivisionBlock.QueryFree :=
  signedBinary_queryFree _ _ divisionBlock_queryFree

end HiddenCircuits.Complexity.BinaryArithmetic
