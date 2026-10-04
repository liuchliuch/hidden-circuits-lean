import HiddenCircuits.Encoding

namespace HiddenCircuits

/-- Every actual encoded operation intertwines the physical word followed by projection. -/
theorem encoded_intertwining {k : ℕ}
    (M : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ) :
    encodingE k * M * globalProjection k = encoded M * encodingE k := by
  unfold encoded
  rw [Matrix.mul_assoc (encodingE k * M) (encodingL k) (encodingE k),encodingLE]

/-- The projected physical action is reconstructed exactly from its encoded operation. -/
theorem projection_sandwich_reconstruction {k : ℕ}
    (M : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ) :
    globalProjection k * M * globalProjection k = encodingL k * encoded M * encodingE k := by
  unfold encoded
  rw [← encodingLE k]
  simp only [Matrix.mul_assoc]

/-- Substitution of any proved encoded matrix gives the exact physical intertwining
identity used after projected locality; the matrix equality is ordinary substitution. -/
theorem encoded_intertwining_of_eq {k : ℕ}
    (M : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ)
    (g : Matrix (CodeBits k) (CodeBits k) ℚ) (h : encoded M = g) :
    encodingE k * M * globalProjection k = g * encodingE k := by
  rw [encoded_intertwining,h]

 theorem projection_sandwich_of_encoded_eq {k : ℕ}
    (M : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ)
    (g : Matrix (CodeBits k) (CodeBits k) ℚ) (h : encoded M = g) :
    globalProjection k * M * globalProjection k = encodingL k * g * encodingE k := by
  rw [projection_sandwich_reconstruction,h]

end HiddenCircuits
