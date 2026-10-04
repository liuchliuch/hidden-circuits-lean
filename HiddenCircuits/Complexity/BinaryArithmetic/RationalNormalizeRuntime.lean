import HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalizeParse

/-! Public endpoints for actual polynomial-time canonical rational normalization.
The raw-word, natural-number-code, and canonical-rational contracts are separate. -/
namespace HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
open OracleBlock

/-- Normalize an arbitrary natural-coded raw pair using the total raw decoder. -/
def naturalCode (n : ℕ) : ℕ := RationalOracleEncoding.code (rawValue (Computability.encodeNat n))

@[simp] theorem rawValue_bits (q : ℚ) : rawValue (RationalOracleEncoding.bits q)=q := by
  rw [RationalOracleEncoding.bits,rawValue_pair]
  exact Rat.num_div_den q

@[simp] theorem rawValue_code (q : ℚ) : rawValue (Computability.encodeNat (RationalOracleEncoding.code q))=q := by
  rw [RationalOracleEncoding.encode_code,rawValue_bits]

/-- Canonical rational codes are fixed points; the arbitrary natural input
contract is instead the separately stated total decoder above. -/
@[simp] theorem naturalCode_canonical (q : ℚ) : naturalCode (RationalOracleEncoding.code q)=RationalOracleEncoding.code q := by
  simp [naturalCode]

theorem naturalCode_idempotent (n : ℕ) : naturalCode (naturalCode n)=naturalCode n := by
  exact naturalCode_canonical _

/-- Physical stack output is the actual natural-number encoding of the canonical
rational code, rather than an unreduced numerator/denominator proxy. -/
theorem rawProgram_executes_code (g : BitString → ℕ) (xs : BitString) :
    ∃c,rawProgram.Executes g (Function.update (fun _=>[]) 0 xs)
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (RationalOracleEncoding.code (rawValue xs)))) c ∧
      c≤rawTime.eval xs.length := by
  simpa only [RationalOracleEncoding.encode_code] using rawProgram_executes g xs

theorem naturalProgram_executes (g : BitString → ℕ) (n : ℕ) :
    ∃c,rawProgram.Executes g (Function.update (fun _=>[]) 0 (Computability.encodeNat n))
      (Function.update (fun _=>[]) 0 (Computability.encodeNat (naturalCode n))) c ∧
      c≤rawTime.eval (Computability.encodeNat n).length :=
  rawProgram_executes_code g (Computability.encodeNat n)

/-- Standard mathlib TM2 machine for every raw word, with no parser, gcd,
divisibility, runtime, or output certificates supplied to its interface. -/
noncomputable def rawComputable :
    Turing.TM2ComputableInPolyTime id id (fun xs=>RationalOracleEncoding.bits (rawValue xs)) :=
  computableOfBlock rawProgram rawProgram_queryFree rawTime (by
    intro xs
    obtain ⟨c,hc,hcb⟩:=rawProgram_executes (fun _=>0) xs
    exact ⟨_,c,hc,by simp,hcb⟩)

/-- The same actual TM2 machine with binary natural-number input and output
encodings; the time bound is polynomial in the input bit length. -/
noncomputable def naturalComputable :
    Turing.TM2ComputableInPolyTime Computability.encodeNat Computability.encodeNat naturalCode :=
  { toTM2ComputableAux := rawComputable.toTM2ComputableAux
    time := rawComputable.time
    outputsFun := by
      intro n
      simpa only [naturalCode,RationalOracleEncoding.encode_code,id_eq] using
        rawComputable.outputsFun (Computability.encodeNat n) }

end HiddenCircuits.Complexity.BinaryArithmetic.RationalNormalize
