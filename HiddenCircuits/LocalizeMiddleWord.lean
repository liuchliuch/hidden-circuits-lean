import HiddenCircuits.ProjectedLocality

namespace HiddenCircuits
open scoped Kronecker

/-- The paper's precise condition that both tracks of a letter lie in the active region. -/
def ActiveMiddle (b r c : ℕ) (l : Letter (blockWidth (b+(r+c)))) : Prop :=
  4*b ≤ l.index.val ∧ l.index.val+1 < 4*(b+r)

/-- Translate a globally specified active letter by subtracting exactly `4*b`. -/
def localizeMiddleLetter (b r c : ℕ) (l : Letter (blockWidth (b+(r+c))))
    (h : ActiveMiddle b r c l) : Letter (blockWidth r) :=
  ⟨l.kind,⟨l.index.val-4*b,by
    have hh := h
    unfold ActiveMiddle at hh
    have hr := blockWidth_eq r
    omega⟩⟩

@[simp] theorem localizeMiddleLetter_kind (b r c : ℕ)
    (l : Letter (blockWidth (b+(r+c)))) (h : ActiveMiddle b r c l) :
    (localizeMiddleLetter b r c l h).kind = l.kind := rfl
@[simp] theorem localizeMiddleLetter_index (b r c : ℕ)
    (l : Letter (blockWidth (b+(r+c)))) (h : ActiveMiddle b r c l) :
    (localizeMiddleLetter b r c l h).index.val = l.index.val-4*b := rfl

/-- The corresponding explicit lift of one isolated active letter. -/
def liftMiddleLetter (b r c : ℕ) (l : Letter (blockWidth r)) :
    Letter (blockWidth (b+(r+c))) :=
  Letter.castTracks (blockWidth_add b (r+c)).symm
    ((Letter.castTracks (blockWidth_add r c).symm (l.inLeft (blockWidth c))).inRight (blockWidth b))

 theorem projectedMiddleWord_eq_map (b r c : ℕ) (w : List (Letter (blockWidth r))) :
    projectedMiddleWord b r c w = w.map (liftMiddleLetter b r c) := by
  simp only [projectedMiddleWord,splitWordLeft,splitWordRight,List.map_map,
    Function.comp_def]
  rfl

/-- Localizing and then lifting restores the exact original global letter. -/
theorem liftMiddleLetter_localize (b r c : ℕ)
    (l : Letter (blockWidth (b+(r+c)))) (h : ActiveMiddle b r c l) :
    liftMiddleLetter b r c (localizeMiddleLetter b r c l h) = l := by
  apply Letter.eq_of_kind_index
  · simp only [liftMiddleLetter,Letter.castTracks_kind,Letter.inRight,Letter.inLeft,
      localizeMiddleLetter]
  · have hh := h
    unfold ActiveMiddle at hh
    simp only [liftMiddleLetter,Letter.castTracks_index,Letter.inRight,rightIndex,
      Letter.inLeft,leftIndex,localizeMiddleLetter,blockWidth_eq]
    omega

/-- The actual isolated word obtained by translating every active index. -/
def localizeMiddleWord (b r c : ℕ) (w : List (Letter (blockWidth (b+(r+c)))))
    (h : ∀ l ∈ w, ActiveMiddle b r c l) : List (Letter (blockWidth r)) :=
  w.pmap (fun l hl => localizeMiddleLetter b r c l hl) h

 theorem localizeMiddleWord_length (b r c : ℕ)
    (w : List (Letter (blockWidth (b+(r+c))))) (h : ∀ l ∈ w, ActiveMiddle b r c l) :
    (localizeMiddleWord b r c w h).length = w.length := by
  simp [localizeMiddleWord]

/-- Every word satisfying the active-index bounds is exactly the lifted isolated word. -/
theorem projectedMiddleWord_localize (b r c : ℕ)
    (w : List (Letter (blockWidth (b+(r+c))))) (h : ∀ l ∈ w, ActiveMiddle b r c l) :
    projectedMiddleWord b r c (localizeMiddleWord b r c w h) = w := by
  rw [projectedMiddleWord_eq_map]
  unfold localizeMiddleWord
  rw [List.map_pmap]
  simp only [liftMiddleLetter_localize,List.pmap_eq_map]
  change w.map id = w
  exact List.map_id w

/-- Projected locality for an arbitrary globally specified word under exactly the
paper's active-index condition, with its isolated word constructed explicitly. -/
theorem grouped_projected_locality_of_indices (b r c : ℕ)
    (w : List (Letter (blockWidth (b+(r+c))))) (h : ∀ l ∈ w, ActiveMiddle b r c l) :
    (globalProjection (b+(r+c)) * wordMatrix (2*(b+(r+c))) w *
      globalProjection (b+(r+c))).submatrix (groupedRawCode b r c) (groupedRawCode b r c) =
    (1 : Matrix (CodeBits b) (CodeBits b) ℚ) ⊗ₖ
      (localProjectedMatrix r (localizeMiddleWord b r c w h) ⊗ₖ
        (1 : Matrix (CodeBits c) (CodeBits c) ℚ)) := by
  have hh := grouped_projected_locality b r c (localizeMiddleWord b r c w h)
  rwa [projectedMiddleWord_localize] at hh

 theorem grouped_projected_locality_columns_of_indices (b r c : ℕ)
    (w : List (Letter (blockWidth (b+(r+c))))) (h : ∀ l ∈ w, ActiveMiddle b r c l) :
    (groupedCodeColumns b r c).transpose * globalProjection (b+(r+c)) *
      wordMatrix (2*(b+(r+c))) w * globalProjection (b+(r+c)) * groupedCodeColumns b r c =
    (1 : Matrix (CodeBits b) (CodeBits b) ℚ) ⊗ₖ
      (((codeColumns r).transpose * globalProjection r *
        wordMatrix (2*r) (localizeMiddleWord b r c w h) * globalProjection r * codeColumns r) ⊗ₖ
          (1 : Matrix (CodeBits c) (CodeBits c) ℚ)) := by
  have hh := grouped_projected_locality_columns b r c (localizeMiddleWord b r c w h)
  rwa [projectedMiddleWord_localize] at hh

end HiddenCircuits
