import HiddenCircuits.Circuit.Runtime.WordEvalHardness
import HiddenCircuits.Complexity.PairSerialization

/-! A canonical rational oracle answer is one natural-valued query response:
a self-delimiting signed numerator followed by its positive signed denominator. -/
namespace HiddenCircuits.Complexity.RationalOracleEncoding
open BinaryArithmetic
lemma canonical_signed {z : ℤ} (hz : z≠0) : Canonical (signedBits z) := by
  refine ⟨canonical_encodeNat _,?_⟩
  intro he
  exact False.elim (hz (Int.natAbs_eq_zero.mp ((encodeNat_eq_nil_iff _).mp he)))
lemma pair_ne_nil (left right : BitString) : pairBits left right≠[] := by cases left <;> simp [pairBits]
lemma canonical_pair (left right : BitString) (hr : Canonical right) (hne : right≠[]) :
    Canonical (pairBits left right) := by
  induction left with
  | nil=>exact ⟨hr,fun h=>False.elim (hne h)⟩
  | cons b bs ih=>
    change Canonical (true::b::pairBits bs right)
    exact ⟨⟨ih,fun h=>False.elim (pair_ne_nil bs right h)⟩,by simp⟩
def bits (q : ℚ) : BitString := pairBits (signedBits q.num) (signedBits (q.den:ℤ))
def code (q : ℚ) : ℕ := BinaryArithmetic.value (bits q)
lemma canonical_bits (q : ℚ) : Canonical (bits q) :=
  canonical_pair _ _ (canonical_signed (by exact_mod_cast q.den_nz)) (by simp [signedBits])
lemma encode_code (q : ℚ) : Computability.encodeNat (code q)=bits q := (canonical_eq_encode (canonical_bits q)).symm
lemma code_injective : Function.Injective code := by
  intro q r h
  have hb:=congrArg Computability.encodeNat h
  simp only [encode_code,bits] at hb
  have hp:=congrArg unpairBits hb
  simp only [unpair_pairBits,Option.some.injEq,Prod.mk.injEq] at hp
  have hn : q.num=r.num := by
    have he:=congrArg (fun (bs : BitString)=>signedNat (bs.headD false) (BinaryArithmetic.value bs.tail)) hp.1
    simpa only [signedBits,List.headD_cons,List.tail_cons,value_encodeNat,signedNat_self] using he
  have hd : q.den=r.den := by
    have he:=congrArg (fun (bs : BitString)=>BinaryArithmetic.value bs.tail) hp.2
    simpa only [signedBits,List.tail_cons,value_encodeNat,Int.natAbs_natCast] using he
  exact Rat.ext hn hd
end HiddenCircuits.Complexity.RationalOracleEncoding
