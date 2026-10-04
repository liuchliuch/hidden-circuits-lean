import HiddenCircuits.ProjectionProducts
import HiddenCircuits.RawCode

/-! Projected locality for actual global transfers. Logical coordinates are grouped
as the left spectator bits, active bits, and right spectator bits. -/
namespace HiddenCircuits
open scoped Kronecker

/-- The actual elementary word on an active middle group of blocks. -/
def projectedMiddleWord (b r c : ℕ) (w : List (Letter (blockWidth r))) :
    List (Letter (blockWidth (b+(r+c)))) :=
  splitWordRight b (r+c) (splitWordLeft r c w)

/-- Grouped actual raw-code coordinates for left, active, and right blocks. -/
def groupedRawCode (b r c : ℕ) (x : CodeBits b × (CodeBits r × CodeBits c)) :
    State (blockWidth (b+(r+c))) (2*(b+(r+c))) :=
  splitState b (r+c) (rawCode b x.1, splitState r c (rawCode r x.2.1,rawCode c x.2.2))

/-- The isolated active-region operation with its actual local projections. -/
def localProjectedMatrix (r : ℕ) (w : List (Letter (blockWidth r))) :
    Matrix (CodeBits r) (CodeBits r) ℚ :=
  (globalProjection r * wordMatrix (2*r) w * globalProjection r).submatrix
    (rawCode r) (rawCode r)

/-- The active factor is literally the paper's coordinate-column compression. -/
theorem localProjectedMatrix_eq_columns (r : ℕ) (w : List (Letter (blockWidth r))) :
    localProjectedMatrix r w = (codeColumns r).transpose * globalProjection r *
      wordMatrix (2*r) w * globalProjection r * codeColumns r := by
  unfold localProjectedMatrix codeColumns
  rw [← coordinateColumns_compress]
  simp only [Matrix.mul_assoc]

/-- Projected locality, in explicit grouped logical coordinates. Neither P nor the
letters are assumed to be local: the proof uses the actual no-return restrictions. -/
theorem grouped_projected_locality (b r c : ℕ) (w : List (Letter (blockWidth r))) :
    (globalProjection (b+(r+c)) *
      wordMatrix (2*(b+(r+c))) (projectedMiddleWord b r c w) *
      globalProjection (b+(r+c))).submatrix (groupedRawCode b r c) (groupedRawCode b r c) =
    (1 : Matrix (CodeBits b) (CodeBits b) ℚ) ⊗ₖ
      (localProjectedMatrix r w ⊗ₖ (1 : Matrix (CodeBits c) (CodeBits c) ℚ)) := by
  ext x y
  have ho := congrFun (congrFun (splitRestrict_projected_right b (r+c) (splitWordLeft r c w))
    (rawCode b x.1,splitState r c (rawCode r x.2.1,rawCode c x.2.2)))
    (rawCode b y.1,splitState r c (rawCode r y.2.1,rawCode c y.2.2))
  have hi := congrFun (congrFun (splitRestrict_projected_left r c w)
    (rawCode r x.2.1,rawCode c x.2.2)) (rawCode r y.2.1,rawCode c y.2.2)
  simp only [splitRestrict,Matrix.submatrix_apply,Matrix.kroneckerMap_apply] at ho hi
  rw [hi,globalProjection_rawCode,globalProjection_rawCode] at ho
  simpa only [projectedMiddleWord,groupedRawCode,Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply,Matrix.one_apply,localProjectedMatrix] using ho

/-- Standard coordinate columns for the three consecutive logical groups. -/
def groupedCodeColumns (b r c : ℕ) :
    Matrix (State (blockWidth (b+(r+c))) (2*(b+(r+c))))
      (CodeBits b × (CodeBits r × CodeBits c)) ℚ :=
  coordinateColumns (groupedRawCode b r c)

/-- The full Cᵀ P M P C identity of projected locality in grouped coordinates. -/
theorem grouped_projected_locality_columns (b r c : ℕ) (w : List (Letter (blockWidth r))) :
    (groupedCodeColumns b r c).transpose * globalProjection (b+(r+c)) *
      wordMatrix (2*(b+(r+c))) (projectedMiddleWord b r c w) *
      globalProjection (b+(r+c)) * groupedCodeColumns b r c =
    (1 : Matrix (CodeBits b) (CodeBits b) ℚ) ⊗ₖ
      (((codeColumns r).transpose * globalProjection r * wordMatrix (2*r) w *
        globalProjection r * codeColumns r) ⊗ₖ (1 : Matrix (CodeBits c) (CodeBits c) ℚ)) := by
  have h := grouped_projected_locality b r c w
  rw [← coordinateColumns_compress,localProjectedMatrix_eq_columns] at h
  simpa only [groupedCodeColumns,Matrix.mul_assoc] using h

/-- Each lifted letter lies strictly inside the declared active middle region. -/
theorem projectedMiddleWord_indices (b r c : ℕ) (w : List (Letter (blockWidth r)))
    (l : Letter (blockWidth (b+(r+c)))) (hl : l ∈ projectedMiddleWord b r c w) :
    4*b ≤ l.index.val ∧ l.index.val+1 < 4*(b+r) := by
  obtain ⟨l₁,hl₁,rfl⟩ := List.mem_map.mp hl
  obtain ⟨l₂,hl₂,rfl⟩ := List.mem_map.mp hl₁
  obtain ⟨l₃,hl₃,rfl⟩ := List.mem_map.mp hl₂
  obtain ⟨l₄,_,rfl⟩ := List.mem_map.mp hl₃
  have hi := l₄.index.isLt
  simp only [Letter.castTracks_index,Letter.inRight,Letter.inLeft,rightIndex,leftIndex,blockWidth_eq] at *
  omega

end HiddenCircuits
