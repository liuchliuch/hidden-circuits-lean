import HiddenCircuits.ProjectionSplit

namespace HiddenCircuits
open scoped BigOperators Kronecker

/-- Particle-count transport of an actual matrix along equality. -/
def matrixCastParticles {n q r : ℕ} (h : q=r)
    (M : Matrix (State n q) (State n q) ℚ) : Matrix (State n r) (State n r) ℚ :=
  M.submatrix (State.castParticles h.symm) (State.castParticles h.symm)

@[simp] theorem matrixCastParticles_mul {n q r : ℕ} (h : q=r)
    (A B : Matrix (State n q) (State n q) ℚ) :
    matrixCastParticles h (A*B) = matrixCastParticles h A * matrixCastParticles h B := by
  subst r
  rfl
@[simp] theorem matrixCastParticles_word {n q r : ℕ} (h : q=r) (w : List (Letter n)) :
    matrixCastParticles h (wordMatrix q w) = wordMatrix r w := by subst r; rfl
@[simp] theorem State.castParticles_prefix {n q r : ℕ} (h : q=r) (S : State n q) (c : ℕ) :
    (State.castParticles h S).prefixCount c = S.prefixCount c := rfl

/-- The full two-group state space, before selecting its fixed-particle diagonal sector. -/
def splitTransport (a b : ℕ)
    (M : Matrix (State (blockWidth (a+b)) (2*(a+b)))
      (State (blockWidth (a+b)) (2*(a+b))) ℚ) :
    Matrix (State (blockWidth a+blockWidth b) (2*a+2*b))
      (State (blockWidth a+blockWidth b) (2*a+2*b)) ℚ :=
  matrixCastTracks (blockWidth_add a b) (matrixCastParticles (by omega) M)

 theorem splitTransport_mul (a b : ℕ)
    (A B : Matrix (State (blockWidth (a+b)) (2*(a+b)))
      (State (blockWidth (a+b)) (2*(a+b))) ℚ) :
    splitTransport a b (A*B) = splitTransport a b A * splitTransport a b B := by
  simp only [splitTransport,matrixCastParticles_mul,matrixCastTracks_mul]

 theorem splitRestrict_eq (a b : ℕ)
    (M : Matrix (State (blockWidth (a+b)) (2*(a+b)))
      (State (blockWidth (a+b)) (2*(a+b))) ℚ) :
    splitRestrict a b M = blockRestrict (splitTransport a b M) := rfl

 theorem splitTransport_prefix (a b c : ℕ)
    (M : Matrix (State (blockWidth (a+b)) (2*(a+b)))
      (State (blockWidth (a+b)) (2*(a+b))) ℚ)
    (hM : ∀ S T, M S T ≠ 0 → T.prefixCount c ≤ S.prefixCount c)
    (S T : State (blockWidth a+blockWidth b) (2*a+2*b))
    (h : splitTransport a b M S T ≠ 0) : T.prefixCount c ≤ S.prefixCount c := by
  have hh := hM
    (State.castParticles (show 2*a+2*b=2*(a+b) by omega)
      (State.castTracks (blockWidth_add a b).symm S))
    (State.castParticles (show 2*a+2*b=2*(a+b) by omega)
      (State.castTracks (blockWidth_add a b).symm T)) h
  simpa only [State.castParticles_prefix,State.castTracks_prefix] using hh

/-- Genuine product restriction for the two half-filled groups, justified by one-way flow. -/
theorem splitRestrict_mul (a b : ℕ)
    (A B : Matrix (State (blockWidth (a+b)) (2*(a+b)))
      (State (blockWidth (a+b)) (2*(a+b))) ℚ)
    (hA : ∀ S T, A S T ≠ 0 → T.prefixCount (blockWidth a) ≤ S.prefixCount (blockWidth a))
    (hB : ∀ S T, B S T ≠ 0 → T.prefixCount (blockWidth a) ≤ S.prefixCount (blockWidth a)) :
    splitRestrict a b (A*B) = splitRestrict a b A * splitRestrict a b B := by
  simp only [splitRestrict_eq,splitTransport_mul]
  exact blockRestrict_mul _ _ (splitTransport_prefix a b (blockWidth a) A hA)
    (splitTransport_prefix a b (blockWidth a) B hB)

 theorem prefixCut_mul {n q : ℕ} (A B : Matrix (State n q) (State n q) ℚ) (c : ℕ)
    (hA : ∀ S T, A S T ≠ 0 → T.prefixCount c ≤ S.prefixCount c)
    (hB : ∀ S T, B S T ≠ 0 → T.prefixCount c ≤ S.prefixCount c) :
    ∀ S T, (A*B) S T ≠ 0 → T.prefixCount c ≤ S.prefixCount c := by
  intro S T h
  rw [Matrix.mul_apply] at h
  obtain ⟨K,_,hK⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (hB K T (fun hz => hK (by rw [hz,mul_zero]))).trans
    (hA S K (fun hz => hK (by rw [hz,zero_mul])))

/-- The actual stabilized power retains one-way flow at every block boundary. -/
theorem globalProjection_prefix_boundary {k : ℕ}
    (S T : State (blockWidth k) (2*k)) (h : globalProjection k S T ≠ 0) (j : ℕ) :
    T.prefixCount (4*j) ≤ S.prefixCount (4*j) :=
  prefixCut_power (globalFilter k (2*k)) (4*j)
    (fun S T h => globalFilter_prefix_boundary S T h j) (globalProjectionExponent k) S T h

/-- Lift a word on the left group to the actual total track space. -/
def splitWordLeft (a b : ℕ) (w : List (Letter (blockWidth a))) : List (Letter (blockWidth (a+b))) :=
  (w.map (Letter.inLeft (blockWidth b))).map (Letter.castTracks (blockWidth_add a b).symm)
/-- Lift a word on the right group to the actual total track space. -/
def splitWordRight (a b : ℕ) (w : List (Letter (blockWidth b))) : List (Letter (blockWidth (a+b))) :=
  (w.map (Letter.inRight (blockWidth a))).map (Letter.castTracks (blockWidth_add a b).symm)

 theorem matrixCastTracks_word_back {n m q : ℕ} (h : n=m) (w : List (Letter m)) :
    matrixCastTracks h (wordMatrix q (w.map (Letter.castTracks h.symm))) = wordMatrix q w := by
  subst m
  change wordMatrix q (w.map id) = wordMatrix q w
  rw [List.map_id]

 theorem splitRestrict_word_left (a b : ℕ) (w : List (Letter (blockWidth a))) :
    splitRestrict a b (wordMatrix (2*(a+b)) (splitWordLeft a b w)) =
      wordMatrix (2*a) w ⊗ₖ (1 : Matrix (State (blockWidth b) (2*b)) (State (blockWidth b) (2*b)) ℚ) := by
  rw [splitRestrict_eq]
  unfold splitTransport splitWordLeft
  rw [matrixCastParticles_word,matrixCastTracks_word_back]
  exact blockRestrict_word_left w

 theorem splitRestrict_word_right (a b : ℕ) (w : List (Letter (blockWidth b))) :
    splitRestrict a b (wordMatrix (2*(a+b)) (splitWordRight a b w)) =
      (1 : Matrix (State (blockWidth a) (2*a)) (State (blockWidth a) (2*a)) ℚ) ⊗ₖ wordMatrix (2*b) w := by
  rw [splitRestrict_eq]
  unfold splitTransport splitWordRight
  rw [matrixCastParticles_word,matrixCastTracks_word_back]
  exact blockRestrict_word_right w

 theorem splitWordLeft_prefix (a b : ℕ) (w : List (Letter (blockWidth a))) :
    ∀ S T, wordMatrix (2*(a+b)) (splitWordLeft a b w) S T ≠ 0 →
      T.prefixCount (blockWidth a) ≤ S.prefixCount (blockWidth a) := by
  apply word_prefix_outside
  intro l hl
  obtain ⟨l₁,hl₁,rfl⟩ := List.mem_map.mp hl
  obtain ⟨l₀,_,rfl⟩ := List.mem_map.mp hl₁
  simpa only [Letter.castTracks_index] using (Letter.left_boundary (b:=blockWidth b) l₀)

 theorem splitWordRight_prefix (a b : ℕ) (w : List (Letter (blockWidth b))) :
    ∀ S T, wordMatrix (2*(a+b)) (splitWordRight a b w) S T ≠ 0 →
      T.prefixCount (blockWidth a) ≤ S.prefixCount (blockWidth a) := by
  apply word_prefix_outside
  intro l hl
  obtain ⟨l₁,hl₁,rfl⟩ := List.mem_map.mp hl
  obtain ⟨l₀,_,rfl⟩ := List.mem_map.mp hl₁
  simpa only [Letter.castTracks_index] using (Letter.right_boundary (a:=blockWidth a) l₀)

/-- Actual projection sandwiches factor across a spectator group on the right. -/
theorem splitRestrict_projected_left (a b : ℕ) (w : List (Letter (blockWidth a))) :
    splitRestrict a b (globalProjection (a+b) *
      wordMatrix (2*(a+b)) (splitWordLeft a b w) * globalProjection (a+b)) =
      (globalProjection a * wordMatrix (2*a) w * globalProjection a) ⊗ₖ globalProjection b := by
  have hp : ∀ S T, globalProjection (a+b) S T ≠ 0 →
      T.prefixCount (blockWidth a) ≤ S.prefixCount (blockWidth a) := by
    intro S T h
    simpa only [blockWidth_eq] using globalProjection_prefix_boundary S T h a
  have hw := splitWordLeft_prefix a b w
  rw [splitRestrict_mul a b _ _ (prefixCut_mul _ _ _ hp hw) hp,
    splitRestrict_mul a b _ _ hp hw,splitRestrict_projection,splitRestrict_word_left,
    ← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,mul_one,globalProjection_idempotent]

/-- Actual projection sandwiches factor across a spectator group on the left. -/
theorem splitRestrict_projected_right (a b : ℕ) (w : List (Letter (blockWidth b))) :
    splitRestrict a b (globalProjection (a+b) *
      wordMatrix (2*(a+b)) (splitWordRight a b w) * globalProjection (a+b)) =
      globalProjection a ⊗ₖ (globalProjection b * wordMatrix (2*b) w * globalProjection b) := by
  have hp : ∀ S T, globalProjection (a+b) S T ≠ 0 →
      T.prefixCount (blockWidth a) ≤ S.prefixCount (blockWidth a) := by
    intro S T h
    simpa only [blockWidth_eq] using globalProjection_prefix_boundary S T h a
  have hw := splitWordRight_prefix a b w
  rw [splitRestrict_mul a b _ _ (prefixCut_mul _ _ _ hp hw) hp,
    splitRestrict_mul a b _ _ hp hw,splitRestrict_projection,splitRestrict_word_right,
    ← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,mul_one,globalProjection_idempotent]

end HiddenCircuits
