import HiddenCircuits.BlockDual

namespace HiddenCircuits
open scoped Kronecker
namespace Letter

def inLeft {a : ℕ} (b : ℕ) (l : Letter a) : Letter (a+b) := ⟨l.kind,leftIndex b l.index⟩
def inRight (a : ℕ) {b : ℕ} (l : Letter b) : Letter (a+b) := ⟨l.kind,rightIndex a l.index⟩

 theorem left_boundary {a b : ℕ} (l : Letter a) : a ≠ (inLeft b l).index.val+1 := by
  have := l.index.isLt
  simp only [inLeft,leftIndex]
  omega
 theorem right_boundary {a b : ℕ} (l : Letter b) : a ≠ (inRight a l).index.val+1 := by
  simp only [inRight,rightIndex]
  omega

@[simp] theorem blockRestrict_inLeft {a b u v : ℕ} (l : Letter a) :
    blockRestrict ((l.inLeft b).matrix (u+v)) = l.matrix u ⊗ₖ (1 : Matrix (State b v) (State b v) ℚ) := by
  cases l with
  | mk kind i =>
    cases kind with
    | R => exact blockRestrict_rise_left a b u v i
    | D => exact blockRestrict_drop_left a b u v i
    | B => exact blockRestrict_dualRise_left a b u v i
    | E => exact blockRestrict_dualDrop_left a b u v i

@[simp] theorem blockRestrict_inRight {a b u v : ℕ} (l : Letter b) :
    blockRestrict ((l.inRight a).matrix (u+v)) = (1 : Matrix (State a u) (State a u) ℚ) ⊗ₖ l.matrix v := by
  cases l with
  | mk kind i =>
    cases kind with
    | R => exact blockRestrict_rise_right a b u v i
    | D => exact blockRestrict_drop_right a b u v i
    | B => exact blockRestrict_dualRise_right a b u v i
    | E => exact blockRestrict_dualDrop_right a b u v i
end Letter

/-- Exact whole-word restriction on the left; no flow may leave and return to this sector. -/
theorem blockRestrict_word_left {a b u v : ℕ} (w : List (Letter a)) :
    blockRestrict (wordMatrix (u+v) (w.map (Letter.inLeft b))) =
      wordMatrix u w ⊗ₖ (1 : Matrix (State b v) (State b v) ℚ) := by
  induction w with
  | nil => simp [Matrix.one_kronecker_one]
  | cons l w ih =>
    rw [List.map_cons,wordMatrix_cons]
    rw [blockRestrict_mul _ _ (fun S T h =>
      letter_prefix_outside (l.inLeft b) S T h a l.left_boundary)
      (word_prefix_outside _ a (by
        intro x hx
        obtain ⟨l,_,rfl⟩ := List.mem_map.mp hx
        exact l.left_boundary))]
    rw [Letter.blockRestrict_inLeft,ih,← Matrix.mul_kronecker_mul,one_mul,wordMatrix_cons]

/-- Exact whole-word restriction on the right; the local dual uses the local complement sector. -/
theorem blockRestrict_word_right {a b u v : ℕ} (w : List (Letter b)) :
    blockRestrict (wordMatrix (u+v) (w.map (Letter.inRight a))) =
      (1 : Matrix (State a u) (State a u) ℚ) ⊗ₖ wordMatrix v w := by
  induction w with
  | nil => simp [Matrix.one_kronecker_one]
  | cons l w ih =>
    rw [List.map_cons,wordMatrix_cons]
    rw [blockRestrict_mul _ _ (fun S T h =>
      letter_prefix_outside (l.inRight a) S T h a l.right_boundary)
      (word_prefix_outside _ a (by
        intro x hx
        obtain ⟨l,_,rfl⟩ := List.mem_map.mp hx
        exact l.right_boundary))]
    rw [Letter.blockRestrict_inRight,ih,← Matrix.mul_kronecker_mul,one_mul,wordMatrix_cons]

/-- A word on a middle consecutive block, using the actual twice-translated indices. -/
def middleWord {b : ℕ} (a c : ℕ) (w : List (Letter b)) : List (Letter (a+(b+c))) :=
  (w.map (Letter.inLeft c)).map (Letter.inRight a)

/-- Full three-part restriction: outside selected states are unchanged, and the inside
coefficient is exactly the isolated local word including B and E. -/
theorem word_middle_entry {a b c u v z : ℕ} (w : List (Letter b))
    (S₀ T₀ : State a u) (S₁ T₁ : State b v) (S₂ T₂ : State c z) :
    wordMatrix (u+(v+z)) (middleWord a c w)
      (State.join S₀ (State.join S₁ S₂)) (State.join T₀ (State.join T₁ T₂)) =
      (if S₀=T₀ then 1 else 0) * wordMatrix v w S₁ T₁ * (if S₂=T₂ then 1 else 0) := by
  have hr := congrFun (congrFun (blockRestrict_word_right (a:=a) (u:=u) (v:=v+z)
    (w.map (Letter.inLeft c))) (S₀,State.join S₁ S₂)) (T₀,State.join T₁ T₂)
  have hl := congrFun (congrFun (blockRestrict_word_left (b:=c) (u:=v) (v:=z) w)
    (S₁,S₂)) (T₁,T₂)
  simp only [blockRestrict,Matrix.submatrix_apply,Matrix.kronecker_apply,Matrix.one_apply] at hr hl
  change _ = _ at hr
  rw [show wordMatrix (u+(v+z)) (middleWord a c w)
      (State.join S₀ (State.join S₁ S₂)) (State.join T₀ (State.join T₁ T₂)) =
    (if S₀=T₀ then 1 else 0) * wordMatrix (v+z) (w.map (Letter.inLeft c))
      (State.join S₁ S₂) (State.join T₁ T₂) from hr, hl,mul_assoc]

end HiddenCircuits
