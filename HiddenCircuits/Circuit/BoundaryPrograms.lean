import HiddenCircuits.Circuit.ConstraintPrograms

/-! Literal linear-size preparation/reset programs on every logical wire. -/
namespace HiddenCircuits.Circuit
open scoped Kronecker

def headPlacement (n : ℕ) : Placement (n+1) 1 := ⟨0,n,by omega⟩
def tailPlacement (n : ℕ) : Placement (n+1) n := ⟨1,0,by omega⟩

lemma rawCode_zero_hasTrack (x : CodeBits 0) (t : ℕ) : ¬(rawCode 0 x).HasTrack t := by
  rintro ⟨h,_⟩
  exact Nat.not_lt_zero t h

lemma headPlacement_equiv (n : ℕ) (i : Fin 2) (x : CodeBits n) :
    (headPlacement n).equiv (PUnit.unit,((i,PUnit.unit),x))=(i,x) := by
  apply rawCode_injective (n+1)
  apply State.ext_hasTrack
  intro t
  rw [placement_raw_hasTrack,rawCode_succ_hasTrack]
  simp [headPlacement,rawCode_succ_hasTrack,rawCode_zero_hasTrack,blockWidth]

lemma tailPlacement_equiv (n : ℕ) (i : Fin 2) (x : CodeBits n) :
    (tailPlacement n).equiv ((i,PUnit.unit),(x,PUnit.unit))=(i,x) := by
  apply rawCode_injective (n+1)
  apply State.ext_hasTrack
  intro t
  rw [placement_raw_hasTrack,rawCode_succ_hasTrack]
  simp [tailPlacement,rawCode_succ_hasTrack,rawCode_zero_hasTrack,blockWidth]

lemma headPlacement_lift (n : ℕ) (g : OneGate) :
    (headPlacement n).lift g.logical = g.matrix ⊗ₖ (1 : Matrix (CodeBits n) (CodeBits n) ℚ) := by
  ext s t
  rcases s with ⟨i,x⟩
  rcases t with ⟨j,y⟩
  have h := Placement.lift_equiv_entry (headPlacement n) g.logical
    (PUnit.unit,((i,PUnit.unit),x)) (PUnit.unit,((j,PUnit.unit),y))
  rw [headPlacement_equiv,headPlacement_equiv] at h
  simpa [OneGate.logical,oneBitEquiv,Matrix.kroneckerMap_apply,Matrix.one_apply] using h

lemma tailPlacement_lift (n : ℕ) (A : Matrix (CodeBits n) (CodeBits n) ℚ) :
    (tailPlacement n).lift A = (1 : Matrix (Fin 2) (Fin 2) ℚ) ⊗ₖ A := by
  ext s t
  rcases s with ⟨i,x⟩
  rcases t with ⟨j,y⟩
  have h := Placement.lift_equiv_entry (tailPlacement n) A
    ((i,PUnit.unit),(x,PUnit.unit)) ((j,PUnit.unit),(y,PUnit.unit))
  rw [tailPlacement_equiv,tailPlacement_equiv] at h
  have he : ((i,PUnit.unit) : CodeBits 1) = (j,PUnit.unit) ↔ i=j := by
    constructor
    · exact fun h => congrArg Prod.fst h
    · intro h; cases h; rfl
  simpa [Matrix.kroneckerMap_apply,Matrix.one_apply,he] using h

/-- The same primitive one-bit operation, literally placed once on every wire. -/
def uniformOneProgram (g : OneGate) : (n : ℕ) → ConstraintProgram n
  | 0 => .identity 0
  | n+1 => (show ConstraintProgram (n+1) from ⟨1,[.one (headPlacement n) g]⟩).compose
      ((uniformOneProgram g n).lift (tailPlacement n))

def uniformOneMatrix (g : OneGate) : (n : ℕ) → Matrix (CodeBits n) (CodeBits n) ℚ
  | 0 => 1
  | n+1 => g.matrix ⊗ₖ uniformOneMatrix g n

@[simp] theorem uniformOneProgram_scalar (g : OneGate) (n : ℕ) :
    (uniformOneProgram g n).scalar=1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [uniformOneProgram,ConstraintProgram.compose,ConstraintProgram.lift,ih]

@[simp] theorem uniformOneProgram_length (g : OneGate) (n : ℕ) :
    (uniformOneProgram g n).gates.length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [uniformOneProgram,ConstraintProgram.compose,ConstraintProgram.lift,ih]

theorem uniformOneProgram_matrix (g : OneGate) (n : ℕ) :
    (uniformOneProgram g n).matrix=uniformOneMatrix g n := by
  induction n with
  | zero => exact ConstraintProgram.identity_matrix 0
  | succ n ih =>
    rw [uniformOneProgram,ConstraintProgram.compose_matrix,ConstraintProgram.lift_matrix,ih]
    have hh : (show ConstraintProgram (n+1) from ⟨1,[.one (headPlacement n) g]⟩).matrix =
        (headPlacement n).lift g.logical := by
      simp [ConstraintProgram.matrix,constraintCircuitMatrix,ConstraintGate.matrix]
    rw [hh,headPlacement_lift,tailPlacement_lift,← Matrix.mul_kronecker_mul]
    simp [uniformOneMatrix]

def preparationProgram (n : ℕ) : ConstraintProgram n := uniformOneProgram .copy n
def resetProgram (n : ℕ) : ConstraintProgram n := uniformOneProgram .reset n

theorem preparationProgram_matrix (n : ℕ) : (preparationProgram n).matrix=preparationMatrix n := by
  rw [preparationProgram,uniformOneProgram_matrix]
  induction n with
  | zero => rfl
  | succ n ih => simp only [uniformOneMatrix,preparationMatrix,ih]

theorem resetProgram_matrix (n : ℕ) : (resetProgram n).matrix=resetMatrix n := by
  rw [resetProgram,uniformOneProgram_matrix]
  induction n with
  | zero => rfl
  | succ n ih => simp only [uniformOneMatrix,resetMatrix,ih]

end HiddenCircuits.Circuit
