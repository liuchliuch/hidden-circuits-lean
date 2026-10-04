import HiddenCircuits.Complexity.BinaryArithmetic.SignedBits

/-! Constant-time canonical sign negation, including the unique encoding of zero. -/
namespace HiddenCircuits.Circuit.Runtime.SpectralCoefficients
open HiddenCircuits.Complexity HiddenCircuits.Complexity.OracleBlock
open HiddenCircuits.Complexity.BinaryArithmetic

 theorem finishSigned_neg (a : ℤ) :
    finishSigned (!(negative a)) (Computability.encodeNat a.natAbs)=signedBits (-a) := by
  rw [finishSigned_encode]
  have he : signedNat (!(negative a)) a.natAbs= -signedNat (negative a) a.natAbs := by
    cases negative a <;> simp [signedNat]
  rw [he,signedNat_self]

noncomputable def negateOn {k : ℕ} (p : Fin (k+1)) : OracleBlock k :=
  branchPop p skip (finishOn p true) (finishOn p false)

theorem negateOn_executes {k : ℕ} (g : BitString → ℕ) (p : Fin (k+1)) (s : Store k)
    (a : ℤ) (hs:s p=signedBits a) :
    ∃ c, (negateOn p).Executes g s (Function.update s p (signedBits (-a))) c ∧ c≤5 := by
  let mag := Computability.encodeNat a.natAbs
  let t := Function.update s p mag
  have hf := finishOn_executes g p (!(negative a)) t
  have he : Function.update t p (finishSigned (!(negative a)) (t p))=
      Function.update s p (signedBits (-a)) := by
    simp [t,mag,finishSigned_neg]
  rw [he] at hf
  have hinput : s p=negative a::mag := hs
  cases hn:negative a with
  | false =>
    rw [hn] at hinput hf
    have hh := branchPop_false p skip (finishOn p true) (finishOn p false) g hinput hf
    exact ⟨finishCost (t p)+2,hh,by have := finishCost_le (t p);omega⟩
  | true =>
    rw [hn] at hinput hf
    have hh := branchPop_true p skip (finishOn p true) (finishOn p false) g hinput hf
    exact ⟨finishCost (t p)+2,hh,by have := finishCost_le (t p);omega⟩

theorem negateOn_queryFree {k : ℕ} (p : Fin (k+1)) : (negateOn p).QueryFree :=
  branchPop_queryFree _ _ _ _ skip_queryFree (finishOn_queryFree _ _) (finishOn_queryFree _ _)
end HiddenCircuits.Circuit.Runtime.SpectralCoefficients
