import HiddenCircuits.Circuit.Placement
import HiddenCircuits.Circuit.ScaledWords
import HiddenCircuits.CanonicalLocality

namespace HiddenCircuits.Circuit
open scoped Kronecker

/-- Translate a literal physical word to the exact four-track region for the placed logical gate. -/
def Placement.liftWord {n r : ℕ} (p : Placement n r)
    (w : List (Letter (blockWidth r))) : List (Letter (blockWidth n)) :=
  (projectedMiddleWord p.before r p.after w).map (Letter.castTracks (congrArg blockWidth p.size))

/-- Physical locality for actual placed circuit gates, proved from the global projector. -/
theorem Placement.liftWord_encoded {n r : ℕ} (p : Placement n r)
    (w : List (Letter (blockWidth r))) :
    encoded (wordMatrix (2*n) (p.liftWord w)) = p.lift (encoded (wordMatrix (2*r) w)) := by
  rcases p with ⟨b,c,h⟩
  subst n
  change encoded (wordMatrix (2*(b+(r+c))) ((projectedMiddleWord b r c w).map id)) =
    logicalExtend b r c (encoded (wordMatrix (2*r) w))
  rw [List.map_id]
  exact projected_locality_global b r c w

 theorem Placement.lift_smul {n r : ℕ} (p : Placement n r) (c : ℚ)
    (A : Matrix (CodeBits r) (CodeBits r) ℚ) : p.lift (c • A)=c • p.lift A := by
  ext x y
  simp only [Placement.lift,Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- Literal-word placement preserves the exact scalar implementation. -/
def ScaledWord.lift {n r : ℕ} (p : Placement n r) (w : ScaledWord r) : ScaledWord n :=
  ⟨w.scalar,p.liftWord w.word⟩

 theorem ScaledWord.lift_matrix {n r : ℕ} (p : Placement n r) (w : ScaledWord r) :
    (w.lift p).matrix=p.lift w.matrix := by
  rw [ScaledWord.lift,ScaledWord.matrix,Placement.liftWord_encoded,← Placement.lift_smul]
  rfl

 theorem Placement.liftWord_length {n r : ℕ} (p : Placement n r)
    (w : List (Letter (blockWidth r))) : (p.liftWord w).length=w.length := by
  simp [Placement.liftWord,projectedMiddleWord,splitWordLeft,splitWordRight]

@[simp] theorem ScaledWord.lift_length {n r : ℕ} (p : Placement n r) (w : ScaledWord r) :
    (w.lift p).word.length=w.word.length := p.liftWord_length w.word

end HiddenCircuits.Circuit
