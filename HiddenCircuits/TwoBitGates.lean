import HiddenCircuits.Small.Gate8Projection
import HiddenCircuits.Small.Gate8Encoded
import HiddenCircuits.Small.Gate8Definitions

namespace HiddenCircuits
open Small
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem twoBitSweep_compressed :
    compress gate8Enum (twoBitFilter 0 * twoBitFilter 1) = Gate8Sweep := by
  rw [twoBitFilter_sweep, compress_smul, compress_word]
  change (1/4096 : ℚ) • ([compress gate8Enum (rise 8 4 1), compress gate8Enum (drop 8 4 2), compress gate8Enum (rise 8 4 2), compress gate8Enum (dualRise 8 4 1), compress gate8Enum (rise 8 4 2),
    compress gate8Enum (rise 8 4 1), compress gate8Enum (rise 8 4 0), compress gate8Enum (dualDrop 8 4 2), compress gate8Enum (drop 8 4 2), compress gate8Enum (rise 8 4 2),
    compress gate8Enum (rise 8 4 1), compress gate8Enum (drop 8 4 2), compress gate8Enum (rise 8 4 2), compress gate8Enum (dualRise 8 4 1), compress gate8Enum (rise 8 4 2),
    compress gate8Enum (rise 8 4 1), compress gate8Enum (rise 8 4 0), compress gate8Enum (dualDrop 8 4 2), compress gate8Enum (drop 8 4 2), compress gate8Enum (rise 8 4 2),
    compress gate8Enum (rise 8 4 5), compress gate8Enum (drop 8 4 6), compress gate8Enum (rise 8 4 6), compress gate8Enum (dualRise 8 4 5), compress gate8Enum (rise 8 4 6),
    compress gate8Enum (rise 8 4 5), compress gate8Enum (rise 8 4 4), compress gate8Enum (dualDrop 8 4 6), compress gate8Enum (drop 8 4 6), compress gate8Enum (rise 8 4 6),
    compress gate8Enum (rise 8 4 5), compress gate8Enum (drop 8 4 6), compress gate8Enum (rise 8 4 6), compress gate8Enum (dualRise 8 4 5), compress gate8Enum (rise 8 4 6),
    compress gate8Enum (rise 8 4 5), compress gate8Enum (rise 8 4 4), compress gate8Enum (dualDrop 8 4 6), compress gate8Enum (drop 8 4 6), compress gate8Enum (rise 8 4 6)]).prod = Gate8Sweep
  simp only [gate8_rise0, gate8_rise1, gate8_rise2, gate8_rise4, gate8_rise5, gate8_rise6,
    gate8_drop2, gate8_drop6, gate8_dualRise1, gate8_dualRise5,
    gate8_dualDrop2, gate8_dualDrop6]
  rw [gate8_suffix0]
  exact gate8_sweep_scale

theorem twoBitProjection_compressed : compress gate8Enum twoBitProjection = Gate8Power6 := by
  have hp (n : ℕ) : compress gate8Enum ((twoBitFilter 0 * twoBitFilter 1) ^ n) =
      Gate8Sweep ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, compress_mul, ih, twoBitSweep_compressed, pow_succ]
  exact (hp 6).trans gate8_power6

/-- Regression guard: the raw zero-code row has a genuine off-balanced-sector tail. -/
theorem twoBitProjection_offbalanced_tail :
    twoBitProjection (twoBitCode 0) (gate8States 61) = -8 := by
  change (compress gate8Enum twoBitProjection) 20 61 = -8
  rw [twoBitProjection_compressed]
  decide +kernel

theorem twoBitEncoded_compressed (w : List (Letter 8)) :
    twoBitEncoded w =
      (Gate8Power6 * compress gate8Enum (wordMatrix 4 w) * Gate8Power6).submatrix
        twoBitCodeIndex twoBitCodeIndex := by
  have h : compress gate8Enum (twoBitProjection * wordMatrix 4 w * twoBitProjection) =
      Gate8Power6 * compress gate8Enum (wordMatrix 4 w) * Gate8Power6 := by
    simp only [compress_mul, twoBitProjection_compressed]
  exact congrArg (fun M => M.submatrix twoBitCodeIndex twoBitCodeIndex) h

/-- The shared-boundary letter has the paper's exact two-bit matrix, with no gate assumption. -/
theorem twoBit_G : twoBitEncoded [⟨.R,3⟩] =
    !![-2,2,-7/2,-6; 0,-3,0,-2; 0,0,2,-4; 0,0,0,1] := by
  rw [twoBitEncoded_compressed, compress_word]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Letter.matrix, gate8_rise3]
  exact gate8_encoded_literal

end HiddenCircuits
