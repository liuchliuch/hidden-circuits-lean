import HiddenCircuits.TwoBitGates
import HiddenCircuits.Small.Gate8GlobalBridge

namespace HiddenCircuits

/-- The named global projection retains the same nonzero off-balanced tail. -/
theorem globalProjection_two_offbalanced_tail :
    globalProjection 2 (rawCode 2 (twoBitLex 0)) (Small.gate8States 61) = -8 := by
  rw [twoBitProjection_global, twoBit_rawCode]
  exact twoBitProjection_offbalanced_tail

/-- Lemma 6.1 for the actual global projection and the actual globally defined code rows. -/
theorem global_twoBit_G :
    ((globalProjection 2 * rise (blockWidth 2) (2*2) ⟨3,by decide⟩ * globalProjection 2).submatrix
      (rawCode 2) (rawCode 2)).submatrix twoBitLexEquiv twoBitLexEquiv =
      !![-2,2,-7/2,-6; 0,-3,0,-2; 0,0,2,-4; 0,0,0,1] := by
  rw [twoBitProjection_global]
  have h : ((twoBitProjection * rise 8 4 3 * twoBitProjection).submatrix
      (rawCode 2) (rawCode 2)).submatrix twoBitLexEquiv twoBitLexEquiv =
      twoBitEncoded [⟨.R,3⟩] := by
    ext a b
    change (twoBitProjection * rise 8 4 3 * twoBitProjection)
      (rawCode 2 (twoBitLex a)) (rawCode 2 (twoBitLex b)) = _
    rw [twoBit_rawCode, twoBit_rawCode]
    simp only [twoBitEncoded, wordMatrix_cons, wordMatrix_nil, Letter.matrix, mul_one,
      Matrix.submatrix_apply]
  exact h.trans twoBit_G

/-- The same identity in the paper's literal C₂ᵀP₂R₃P₂C₂ matrix notation. -/
theorem global_twoBit_G_columns :
    ((codeColumns 2).transpose *
      (globalProjection 2 * rise (blockWidth 2) (2*2) ⟨3,by decide⟩ * globalProjection 2) * codeColumns 2).submatrix
        twoBitLexEquiv twoBitLexEquiv =
      !![-2,2,-7/2,-6; 0,-3,0,-2; 0,0,2,-4; 0,0,0,1] := by
  simpa only [codeColumns, coordinateColumns_compress] using global_twoBit_G

end HiddenCircuits
