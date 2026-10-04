import HiddenCircuits.RawCode
import HiddenCircuits.ProjectionEncoding

namespace HiddenCircuits

/-- The concrete E_k=C_kᵀP_k. -/
def encodingE (k : ℕ) : Matrix (CodeBits k) (State (blockWidth k) (2*k)) ℚ :=
  (codeColumns k).transpose * globalProjection k

/-- The concrete L_k=P_kC_k. -/
def encodingL (k : ℕ) : Matrix (State (blockWidth k) (2*k)) (CodeBits k) ℚ :=
  globalProjection k * codeColumns k

/-- The actual encoded operation, without an assumed local action. -/
def encoded {k : ℕ} (M : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ) :
    Matrix (CodeBits k) (CodeBits k) ℚ := encodingE k * M * encodingL k

 theorem encoding_factorization (k : ℕ) :
    encodingL k * encodingE k = globalProjection k ∧ encodingE k * encodingL k = 1 := by
  apply projection_code_factorization _ _ (globalProjection_idempotent k) (codeColumns_projection k)
  rw [globalProjection_rank,codeBits_card]

 theorem encodingEL (k : ℕ) : encodingE k * encodingL k = 1 := (encoding_factorization k).2
 theorem encodingLE (k : ℕ) : encodingL k * encodingE k = globalProjection k := (encoding_factorization k).1

 theorem encodingE_projection (k : ℕ) : encodingE k * globalProjection k = encodingE k := by
  unfold encodingE
  rw [Matrix.mul_assoc,globalProjection_idempotent]

 theorem projection_encodingL (k : ℕ) : globalProjection k * encodingL k = encodingL k := by
  unfold encodingL
  rw [← Matrix.mul_assoc,globalProjection_idempotent]

/-- Exact finite-list encoded composition, retaining an actual P_k at every physical interface. -/
theorem encoded_composition (k : ℕ)
    (w : List (Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ)) :
    encodingE k * projectedWord (globalProjection k) w * encodingL k = (w.map encoded).prod :=
  encoded_word_composition _ _ _ (globalProjection_idempotent k) (encodingE_projection k)
    (encodingEL k) (encodingLE k) w

/-- The encoded action is exactly the physical P_k M P_k entry at raw code states. -/
theorem encoded_entry {k : ℕ}
    (M : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ)
    (x y : CodeBits k) : encoded M x y =
      (globalProjection k * M * globalProjection k) (rawCode k x) (rawCode k y) := by
  have h := congrFun (congrFun (coordinateColumns_compress (rawCode k)
    (globalProjection k * M * globalProjection k)) x) y
  change ((codeColumns k).transpose * (globalProjection k * M * globalProjection k) * codeColumns k) x y = _ at h
  simpa only [encoded,encodingE,encodingL,Matrix.mul_assoc] using h

/-- Multiplication of encodings inserts the actual projector, so powers of raw words cannot silently replace projected powers. -/
theorem encoded_mul {k : ℕ}
    (M N : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ) :
    encoded M * encoded N = encoded (M * globalProjection k * N) := by
  unfold encoded
  rw [← encodingLE]
  simp only [Matrix.mul_assoc]

end HiddenCircuits
