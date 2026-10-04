import HiddenCircuits.Complexity.RationalOracleEncoding

/-! Canonical rational arithmetic is derived from gcd, with no externally
supplied divisibility or size certificate. The runtime implements these identities. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize

def divisor (u v : ℤ) : ℤ := (Nat.gcd u.natAbs v.natAbs:ℤ)
lemma divisor_eq (u v : ℤ) : divisor u v=(Int.gcd u v:ℤ) := rfl
lemma divisor_positive (u v : ℤ) (hv : v≠0) : 0<divisor u v := by
  rw [divisor_eq]
  exact_mod_cast Int.gcd_pos_of_ne_zero_right u hv
lemma divisor_ne_zero (u v : ℤ) (hv : v≠0) : divisor u v≠0 := ne_of_gt (divisor_positive u v hv)
lemma divisor_dvd_left (u v : ℤ) : divisor u v∣u := Int.gcd_dvd_left u v
lemma divisor_dvd_right (u v : ℤ) : divisor u v∣v := Int.gcd_dvd_right u v

lemma numerator_eq (u v : ℤ) (hv : v≠0) :
    ((u:ℚ)/(v:ℚ)).num=if v<0 then -(u/divisor u v) else u/divisor u v := by
  rw [Rat.intCast_div_eq_divInt,Rat.num_divInt,Int.gcd_comm v u]
  change v.sign*u/divisor u v=_
  by_cases hn:v<0
  · rw [if_pos hn,Int.sign_eq_neg_one_of_neg hn,neg_one_mul,Int.neg_ediv_of_dvd (divisor_dvd_left u v)]
  · rw [if_neg hn,Int.sign_eq_one_of_pos (by omega : 0<v),one_mul]

lemma denominator_eq (u v : ℤ) (hv : v≠0) :
    (((u:ℚ)/(v:ℚ)).den:ℤ)=if v<0 then -(v/divisor u v) else v/divisor u v := by
  rw [Rat.intCast_div_eq_divInt,Rat.den_divInt,if_neg hv,Int.gcd_comm v u,Int.natCast_ediv]
  change (v.natAbs:ℤ)/divisor u v=_
  by_cases hn:v<0
  · rw [if_pos hn,Int.ofNat_natAbs_of_nonpos hn.le,Int.neg_ediv_of_dvd (divisor_dvd_right u v)]
  · rw [if_neg hn,Int.natAbs_of_nonneg (by omega)]

lemma quotient_bits_le (u d : ℤ) : (signedBits (u/d)).length ≤ (signedBits u).length := by
  have h:=Nat.size_le_size (Int.natAbs_ediv_le_natAbs u d)
  simpa only [signedBits,List.length_cons,encodeNat_length] using Nat.add_le_add_right h 1
lemma divisor_bits_le (u v : ℤ) (hv : v≠0) :
    (signedBits (divisor u v)).length ≤ (signedBits v).length := by
  have h:=Nat.gcd_le_right u.natAbs (Int.natAbs_pos.mpr hv)
  have hs:=Nat.size_le_size h
  simpa only [divisor,signedBits,List.length_cons,encodeNat_length,Int.natAbs_natCast] using Nat.add_le_add_right hs 1
lemma bits_bounds (u v : ℤ) (hv : v≠0) :
    (signedBits (divisor u v)).length ≤ (signedBits u).length+(signedBits v).length+1 ∧
    (signedBits (u/divisor u v)).length ≤ (signedBits u).length+(signedBits v).length+1 ∧
    (signedBits (v/divisor u v)).length ≤ (signedBits u).length+(signedBits v).length+1 := by
  have hd:=divisor_bits_le u v hv
  have hu:=quotient_bits_le u (divisor u v)
  have hv':=quotient_bits_le v (divisor u v)
  exact ⟨by omega,by omega,by omega⟩
end HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
