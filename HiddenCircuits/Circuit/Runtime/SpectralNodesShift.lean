import HiddenCircuits.Circuit.Runtime.SpectralNodesCell

namespace HiddenCircuits.Circuit.Runtime.SpectralNodes
open HiddenCircuits.Complexity HiddenCircuits.Complexity.BinaryArithmetic

theorem encode_four_mul (n : ℕ) (hn : 0<n) :
    Computability.encodeNat (4*n)=false::false::Computability.encodeNat n := by
  symm
  apply canonical_injective _ (canonical_encodeNat _) _
  · simp [canonical_cons,encodeNat_eq_nil_iff,ne_of_gt hn]
  · simp [value,bitVal]
    omega

theorem signed_four_mul (n : ℕ) (hn : 0<n) :
    signedBits ((n:ℤ)*4)=[false,false]++signedBits (n:ℤ) := by
  have he : (n:ℤ)*4=((4*n:ℕ):ℤ) := by push_cast;ring
  rw [he]
  simp only [signedBits,negative,Int.natCast_nonneg,not_lt,decide_false,Int.natAbs_natCast]
  rw [encode_four_mul n hn]
  rfl
end HiddenCircuits.Circuit.Runtime.SpectralNodes
