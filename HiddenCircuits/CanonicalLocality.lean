import HiddenCircuits.LocalizeMiddleWord
import HiddenCircuits.LogicalConcat
import HiddenCircuits.ProjectedIntertwining

/-! Projected locality on the actual canonical logical bit strings. -/
namespace HiddenCircuits
open scoped Kronecker

 theorem localProjectedMatrix_eq_encoded (r : ℕ) (w : List (Letter (blockWidth r))) :
    localProjectedMatrix r w = encoded (wordMatrix (2*r) w) := by
  ext x y
  exact (encoded_entry _ x y).symm

/-- The paper's projected locality identity under the explicit canonical grouping
of the left, active, and right logical bits. -/
theorem projected_locality (b r c : ℕ) (w : List (Letter (blockWidth r))) :
    (encoded (wordMatrix (2*(b+(r+c))) (projectedMiddleWord b r c w))).submatrix
      (codeTripleConcatEquiv b r c) (codeTripleConcatEquiv b r c) =
    (1 : Matrix (CodeBits b) (CodeBits b) ℚ) ⊗ₖ
      (encoded (wordMatrix (2*r) w) ⊗ₖ (1 : Matrix (CodeBits c) (CodeBits c) ℚ)) := by
  have h := grouped_projected_locality b r c w
  rw [localProjectedMatrix_eq_encoded] at h
  ext x y
  have hh := congrFun (congrFun h x) y
  simpa only [Matrix.submatrix_apply,encoded_entry,rawCode_triple_concat,groupedRawCode] using hh

/-- Tensor extension to the full canonical CodeBits space, with the exact consecutive
logical concatenation rather than an assumed tensor identification. -/
def logicalExtend (b r c : ℕ) (g : Matrix (CodeBits r) (CodeBits r) ℚ) :
    Matrix (CodeBits (b+(r+c))) (CodeBits (b+(r+c))) ℚ :=
  ((1 : Matrix (CodeBits b) (CodeBits b) ℚ) ⊗ₖ
    (g ⊗ₖ (1 : Matrix (CodeBits c) (CodeBits c) ℚ))).submatrix
    (codeTripleConcatEquiv b r c).symm (codeTripleConcatEquiv b r c).symm

/-- Full-space canonical version of Lemma 5.4 for an arbitrary lifted local word. -/
theorem projected_locality_global (b r c : ℕ) (w : List (Letter (blockWidth r))) :
    encoded (wordMatrix (2*(b+(r+c))) (projectedMiddleWord b r c w)) =
      logicalExtend b r c (encoded (wordMatrix (2*r) w)) := by
  ext x y
  have h := congrFun (congrFun (projected_locality b r c w)
    ((codeTripleConcatEquiv b r c).symm x)) ((codeTripleConcatEquiv b r c).symm y)
  simpa only [logicalExtend,Matrix.submatrix_apply,Equiv.apply_symm_apply] using h

/-- Exact projected locality for any global word satisfying the paper's index bounds.
The local word is obtained by subtracting the active region's track offset. -/
theorem projected_locality_of_indices (b r c : ℕ)
    (w : List (Letter (blockWidth (b+(r+c))))) (h : ∀ l ∈ w, ActiveMiddle b r c l) :
    encoded (wordMatrix (2*(b+(r+c))) w) =
      logicalExtend b r c (encoded (wordMatrix (2*r) (localizeMiddleWord b r c w h))) := by
  have hh := projected_locality_global b r c (localizeMiddleWord b r c w h)
  rwa [projectedMiddleWord_localize] at hh

/-- The actual encoded row action and the physical projected action agree with the
isolated active operation tensored with spectator identities. -/
theorem projected_locality_intertwining (b r c : ℕ)
    (w : List (Letter (blockWidth (b+(r+c))))) (h : ∀ l ∈ w, ActiveMiddle b r c l) :
    (encodingE (b+(r+c)) * wordMatrix (2*(b+(r+c))) w * globalProjection (b+(r+c)) =
      logicalExtend b r c (encoded (wordMatrix (2*r) (localizeMiddleWord b r c w h))) *
        encodingE (b+(r+c))) ∧
    (globalProjection (b+(r+c)) * wordMatrix (2*(b+(r+c))) w * globalProjection (b+(r+c)) =
      encodingL (b+(r+c)) *
        logicalExtend b r c (encoded (wordMatrix (2*r) (localizeMiddleWord b r c w h))) *
          encodingE (b+(r+c))) :=
  ⟨encoded_intertwining_of_eq _ _ (projected_locality_of_indices b r c w h),
    projection_sandwich_of_encoded_eq _ _ (projected_locality_of_indices b r c w h)⟩

end HiddenCircuits
