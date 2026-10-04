import HiddenCircuits.GlobalStabilization

namespace HiddenCircuits

/-- Repetition of the actual listed word agrees with matrix exponentiation. -/
theorem wordMatrix_repeat {n q : ℕ} (w : List (Letter n)) (r : ℕ) :
    wordMatrix q (List.replicate r w).flatten = (wordMatrix q w)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [List.replicate_succ,List.flatten_cons,wordMatrix_append,ih,pow_succ']

/-- The literal word underlying the polynomial-power global projection. -/
def globalProjectionWord (k : ℕ) : List (Letter (blockWidth k)) :=
  (List.replicate (globalProjectionExponent k) (globalFilterWord k)).flatten

/-- No abstract operation is needed to express the projection: it is a scalar times
this explicit concatenation of elementary globally normalized R/D/B/E letters. -/
theorem globalProjection_eq_word (k : ℕ) :
    globalProjection k = ((1/64 : ℚ)^(k*globalProjectionExponent k)) •
      wordMatrix (2*k) (globalProjectionWord k) := by
  unfold globalProjection globalFilter
  rw [smul_pow,← pow_mul]
  simp only [globalProjectionWord,wordMatrix_repeat]

/-- Exact number of elementary letters in the paper's projection word. -/
theorem globalProjectionWord_length (k : ℕ) :
    (globalProjectionWord k).length = 20*k*(2*k*(k-1)+2) := by
  simp only [globalProjectionWord,List.length_flatten,List.map_replicate,List.sum_replicate,
    globalFilterWord_length,globalProjectionExponent,nsmul_eq_mul,Nat.cast_id]
  ring

/-- A concrete cubic upper bound on the length of the literal projection word. -/
theorem globalProjectionWord_length_bound (k : ℕ) :
    (globalProjectionWord k).length ≤ 40*k^3+40*k := by
  rw [globalProjectionWord_length]
  calc
    20*k*(2*k*(k-1)+2) ≤ 20*k*(2*k*k+2) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le k 1)) _)
    _ = 40*k^3+40*k := by ring

end HiddenCircuits
