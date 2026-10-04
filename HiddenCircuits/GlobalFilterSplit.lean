import HiddenCircuits.GlobalStabilization
import HiddenCircuits.TrackTransport

namespace HiddenCircuits
open scoped Kronecker

 theorem blockWidth_add (a b : ℕ) : blockWidth (a+b) = blockWidth a + blockWidth b := by
  simp only [blockWidth_eq]
  omega

/-- The actual global word placed at a specified offset in a fixed ambient space. -/
def placedFilterWord (k N o : ℕ) (h : o+blockWidth k ≤ N) : List (Letter N) :=
  (globalFilterWord k).map (Letter.embed N o h)

 theorem placedFilterWord_congr {k l N o : ℕ} (he : k=l)
    (h : o+blockWidth k ≤ N) (h' : o+blockWidth l ≤ N) :
    placedFilterWord k N o h = placedFilterWord l N o h' := by subst l; rfl
 theorem placedFilterWord_offset {k N o p : ℕ} (he : o=p)
    (h : o+blockWidth k ≤ N) (h' : p+blockWidth k ≤ N) :
    placedFilterWord k N o h = placedFilterWord k N p h' := by subst p; rfl

 theorem placedFilterWord_succ (k N o : ℕ) (h : o+blockWidth (k+1) ≤ N) :
    placedFilterWord (k+1) N o h =
      filterWord.map (Letter.embed N o (by change o+(4+blockWidth k) ≤ N at h; omega)) ++
      placedFilterWord k N (o+4) (by change o+(4+blockWidth k) ≤ N at h; omega) := by
  simp only [placedFilterWord,globalFilterWord,List.map_append,List.map_map,
    Function.comp_def,Letter.embed_inLeft,Letter.embed_inRight]

/-- The literal global word splits into the filters on two consecutive groups of blocks. -/
theorem globalFilterWord_embed_split (a b : ℕ) : ∀ N o (h : o+blockWidth (a+b) ≤ N),
    (globalFilterWord (a+b)).map (Letter.embed N o h) =
      (globalFilterWord a).map (Letter.embed N o (by rw [blockWidth_add] at h; omega)) ++
      (globalFilterWord b).map (Letter.embed N (o+blockWidth a) (by rw [blockWidth_add] at h; omega)) := by
  induction a with
  | zero =>
    intro N o h
    exact placedFilterWord_congr (Nat.zero_add b) h _
  | succ a ih =>
    intro N o h
    change placedFilterWord (a+1+b) N o h =
      placedFilterWord (a+1) N o _ ++ placedFilterWord b N (o+blockWidth (a+1)) _
    have hh : o+4+blockWidth (a+b) ≤ N := by
      rw [blockWidth_eq] at h ⊢
      omega
    rw [placedFilterWord_congr (show a+1+b=(a+b)+1 by omega) h
      (show o+blockWidth ((a+b)+1) ≤ N by change o+(4+blockWidth (a+b)) ≤ N; omega),
      placedFilterWord_succ]
    have hi := ih N (o+4) hh
    change placedFilterWord (a+b) N (o+4) hh = _ at hi
    rw [hi,placedFilterWord_succ,List.append_assoc]
    congr 2
    exact placedFilterWord_offset (by simp only [blockWidth]; omega) _ _

/-- The split-word formula in the actual two-region track space. -/
theorem globalFilterWord_split (a b : ℕ) :
    (globalFilterWord (a+b)).map (Letter.castTracks (blockWidth_add a b)) =
      (globalFilterWord a).map (Letter.inLeft (blockWidth b)) ++
      (globalFilterWord b).map (Letter.inRight (blockWidth a)) := by
  have h := globalFilterWord_embed_split a b (blockWidth a+blockWidth b) 0
    (by rw [blockWidth_add]; omega)
  have h₀ : Letter.embed (blockWidth a+blockWidth b) 0
      (show 0+blockWidth (a+b) ≤ blockWidth a+blockWidth b by rw [blockWidth_add]; omega) =
      Letter.castTracks (blockWidth_add a b) := by
    funext l
    apply Letter.eq_of_kind_index
    · simp [Letter.embed]
    · simp [Letter.embed]
  have h₁ : Letter.embed (blockWidth a+blockWidth b) 0
      (show 0+blockWidth a ≤ blockWidth a+blockWidth b by omega) =
      Letter.inLeft (blockWidth b) := by
    funext l
    apply Letter.eq_of_kind_index <;> simp [Letter.embed,Letter.inLeft,leftIndex]
  have h₂ : Letter.embed (blockWidth a+blockWidth b) (0+blockWidth a)
      (show 0+blockWidth a+blockWidth b ≤ blockWidth a+blockWidth b by omega) =
      Letter.inRight (blockWidth a) := by
    funext l
    apply Letter.eq_of_kind_index <;> simp [Letter.embed,Letter.inRight,rightIndex]
  rw [h₀,h₁,h₂] at h
  exact h

/-- The exact two-region diagonal restriction of one actual global-filter pass. -/
theorem blockRestrict_globalFilter_split (a b u v : ℕ) :
    blockRestrict (matrixCastTracks (blockWidth_add a b) (globalFilter (a+b) (u+v))) =
      globalFilter a u ⊗ₖ globalFilter b v := by
  unfold globalFilter
  rw [matrixCastTracks_smul,matrixCastTracks_word,globalFilterWord_split,
    wordMatrix_append,blockRestrict_smul]
  rw [blockRestrict_mul _ _
    (word_prefix_outside _ (blockWidth a) (by
      intro l hl
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hl
      exact l.left_boundary))
    (word_prefix_outside _ (blockWidth a) (by
      intro l hl
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hl
      exact l.right_boundary))]
  rw [blockRestrict_word_left,blockRestrict_word_right,← Matrix.mul_kronecker_mul,
    mul_one,one_mul,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,pow_add]

end HiddenCircuits
