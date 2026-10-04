import HiddenCircuits.BlockRestriction

namespace HiddenCircuits
open scoped Kronecker

/-- Position of a letter internal to the left consecutive block. -/
def leftIndex {a : ℕ} (b : ℕ) (i : Fin (a-1)) : Fin (a+b-1) :=
  ⟨i.val,by have := i.isLt; omega⟩
/-- Position of a letter internal to the right consecutive block. -/
def rightIndex (a : ℕ) {b : ℕ} (i : Fin (b-1)) : Fin (a+b-1) :=
  ⟨a+i.val,by have := i.isLt; omega⟩

@[simp] theorem addedCut_left_left {a b : ℕ} (i : Fin (a-1)) :
    (addedCut (leftIndex b i)).submatrix (Fin.castAdd b) (Fin.castAdd b) = addedCut i := by
  ext x y
  simp only [Matrix.submatrix_apply,addedCut,leftIndex,Fin.val_castAdd,upper,Fin.le_def]

@[simp] theorem addedCut_left_right {a b : ℕ} (i : Fin (a-1)) :
    (addedCut (leftIndex b i)).submatrix (Fin.natAdd a) (Fin.natAdd a) = upper b := by
  ext x y
  have hi := i.isLt
  simp only [Matrix.submatrix_apply,addedCut,leftIndex,Fin.val_natAdd,upper,Fin.le_def]
  rw [if_neg (by omega)]
  simp only [Nat.add_le_add_iff_left]

 theorem addedCut_left_upper {a b : ℕ} (i : Fin (a-1)) (x : Fin b) (y : Fin a) :
    addedCut (leftIndex b i) (Fin.natAdd a x) (Fin.castAdd b y) = 0 := by
  have hi := i.isLt
  have hy := y.isLt
  simp only [addedCut,leftIndex,Fin.val_natAdd,Fin.val_castAdd,upper,Fin.le_def]
  rw [if_neg (by omega),if_neg (by omega)]

@[simp] theorem addedCut_right_left {a b : ℕ} (i : Fin (b-1)) :
    (addedCut (rightIndex a i)).submatrix (Fin.castAdd b) (Fin.castAdd b) = upper a := by
  ext x y
  have hx := x.isLt
  simp only [Matrix.submatrix_apply,addedCut,rightIndex,Fin.val_castAdd,upper,Fin.le_def]
  rw [if_neg (by omega)]

@[simp] theorem addedCut_right_right {a b : ℕ} (i : Fin (b-1)) :
    (addedCut (rightIndex a i)).submatrix (Fin.natAdd a) (Fin.natAdd a) = addedCut i := by
  ext x y
  simp only [Matrix.submatrix_apply,addedCut,rightIndex,Fin.val_natAdd,upper,Fin.le_def,
    Nat.add_le_add_iff_left,Nat.add_assoc,Nat.add_left_cancel_iff]

 theorem addedCut_right_upper {a b : ℕ} (i : Fin (b-1)) (x : Fin b) (y : Fin a) :
    addedCut (rightIndex a i) (Fin.natAdd a x) (Fin.castAdd b y) = 0 := by
  have hy := y.isLt
  simp only [addedCut,rightIndex,Fin.val_natAdd,Fin.val_castAdd,upper,Fin.le_def]
  rw [if_neg (by omega),if_neg (by omega)]

@[simp] theorem deletedCut_left_left {a b : ℕ} (i : Fin (a-1)) :
    (deletedCut (leftIndex b i)).submatrix (Fin.castAdd b) (Fin.castAdd b) = deletedCut i := by
  ext x y
  simp only [Matrix.submatrix_apply,deletedCut,leftIndex,Fin.val_castAdd,upper,Fin.le_def]

@[simp] theorem deletedCut_left_right {a b : ℕ} (i : Fin (a-1)) :
    (deletedCut (leftIndex b i)).submatrix (Fin.natAdd a) (Fin.natAdd a) = upper b := by
  ext x y
  have hi := i.isLt
  simp only [Matrix.submatrix_apply,deletedCut,leftIndex,Fin.val_natAdd,upper,Fin.le_def]
  rw [if_neg (by omega)]
  simp only [Nat.add_le_add_iff_left]

 theorem deletedCut_left_upper {a b : ℕ} (i : Fin (a-1)) (x : Fin b) (y : Fin a) :
    deletedCut (leftIndex b i) (Fin.natAdd a x) (Fin.castAdd b y) = 0 := by
  have hi := i.isLt
  have hy := y.isLt
  simp only [deletedCut,leftIndex,Fin.val_natAdd,Fin.val_castAdd,upper,Fin.le_def]
  rw [if_neg (by omega),if_neg (by omega)]

@[simp] theorem deletedCut_right_left {a b : ℕ} (i : Fin (b-1)) :
    (deletedCut (rightIndex a i)).submatrix (Fin.castAdd b) (Fin.castAdd b) = upper a := by
  ext x y
  have hx := x.isLt
  simp only [Matrix.submatrix_apply,deletedCut,rightIndex,Fin.val_castAdd,upper,Fin.le_def]
  rw [if_neg (by omega)]

@[simp] theorem deletedCut_right_right {a b : ℕ} (i : Fin (b-1)) :
    (deletedCut (rightIndex a i)).submatrix (Fin.natAdd a) (Fin.natAdd a) = deletedCut i := by
  ext x y
  simp only [Matrix.submatrix_apply,deletedCut,rightIndex,Fin.val_natAdd,upper,Fin.le_def,
    Nat.add_le_add_iff_left,Nat.add_assoc,Nat.add_left_cancel_iff]

 theorem deletedCut_right_upper {a b : ℕ} (i : Fin (b-1)) (x : Fin b) (y : Fin a) :
    deletedCut (rightIndex a i) (Fin.natAdd a x) (Fin.castAdd b y) = 0 := by
  have hy := y.isLt
  simp only [deletedCut,rightIndex,Fin.val_natAdd,Fin.val_castAdd,upper,Fin.le_def]
  rw [if_neg (by omega),if_neg (by omega)]

/-- Normalization cancels the exterior upper-cut factor exactly. -/
theorem blockRestrict_rise_left (a b u v : ℕ) (i : Fin (a-1)) :
    blockRestrict (rise (a+b) (u+v) (leftIndex b i)) = rise a u i ⊗ₖ (1 : Matrix (State b v) (State b v) ℚ) := by
  unfold rise
  rw [blockRestrict_mul _ _ (fun S T h => by
      have hi := i.isLt
      have hh := addedCut_prefix_bound (leftIndex b i) S T h a
      simpa only [leftIndex,if_neg (show a ≠ i.val+1 by omega),add_zero] using hh)
    (fun S T h => upperInverse_prefix_flow (a+b) (u+v) S T h a)]
  rw [blockRestrict_compound _ (addedCut_left_upper i),addedCut_left_left,addedCut_left_right,
    blockRestrict_upperInverse,← Matrix.mul_kronecker_mul,mul_upperInverse]

theorem blockRestrict_rise_right (a b u v : ℕ) (i : Fin (b-1)) :
    blockRestrict (rise (a+b) (u+v) (rightIndex a i)) = (1 : Matrix (State a u) (State a u) ℚ) ⊗ₖ rise b v i := by
  unfold rise
  rw [blockRestrict_mul _ _ (fun S T h => by
      have hh := addedCut_prefix_bound (rightIndex a i) S T h a
      simpa only [rightIndex,if_neg (show a ≠ a+i.val+1 by omega),add_zero] using hh)
    (fun S T h => upperInverse_prefix_flow (a+b) (u+v) S T h a)]
  rw [blockRestrict_compound _ (addedCut_right_upper i),addedCut_right_left,addedCut_right_right,
    blockRestrict_upperInverse,← Matrix.mul_kronecker_mul,mul_upperInverse]

theorem blockRestrict_drop_left (a b u v : ℕ) (i : Fin (a-1)) :
    blockRestrict (drop (a+b) (u+v) (leftIndex b i)) = drop a u i ⊗ₖ (1 : Matrix (State b v) (State b v) ℚ) := by
  unfold drop
  rw [blockRestrict_mul _ _ (fun S T h => deletedCut_prefix_flow (leftIndex b i) S T h a)
    (fun S T h => upperInverse_prefix_flow (a+b) (u+v) S T h a)]
  rw [blockRestrict_compound _ (deletedCut_left_upper i),deletedCut_left_left,deletedCut_left_right,
    blockRestrict_upperInverse,← Matrix.mul_kronecker_mul,mul_upperInverse]

theorem blockRestrict_drop_right (a b u v : ℕ) (i : Fin (b-1)) :
    blockRestrict (drop (a+b) (u+v) (rightIndex a i)) = (1 : Matrix (State a u) (State a u) ℚ) ⊗ₖ drop b v i := by
  unfold drop
  rw [blockRestrict_mul _ _ (fun S T h => deletedCut_prefix_flow (rightIndex a i) S T h a)
    (fun S T h => upperInverse_prefix_flow (a+b) (u+v) S T h a)]
  rw [blockRestrict_compound _ (deletedCut_right_upper i),deletedCut_right_left,deletedCut_right_right,
    blockRestrict_upperInverse,← Matrix.mul_kronecker_mul,mul_upperInverse]

end HiddenCircuits
