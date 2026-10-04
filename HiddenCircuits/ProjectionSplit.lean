import HiddenCircuits.GlobalFilterSplit

namespace HiddenCircuits
open scoped BigOperators Kronecker

/-- One-way flow at one cut is preserved by arbitrary matrix powers. -/
theorem prefixCut_power {n q : ℕ} (A : Matrix (State n q) (State n q) ℚ) (c : ℕ)
    (hA : ∀ S T, A S T ≠ 0 → T.prefixCount c ≤ S.prefixCount c) :
    ∀ r S T, (A^r) S T ≠ 0 → T.prefixCount c ≤ S.prefixCount c := by
  intro r
  induction r with
  | zero =>
    intro S T h
    exact PrefixFlow.one S T h c
  | succ r ih =>
    intro S T h
    rw [pow_succ,Matrix.mul_apply] at h
    obtain ⟨K,_,hK⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact (hA K T (fun hz => hK (by rw [hz,mul_zero]))).trans
      (ih S K (fun hz => hK (by rw [hz,zero_mul])))

/-- Restriction of a power is the power of the restriction when the cut has no return. -/
theorem blockRestrict_power {a b u v : ℕ}
    (A : Matrix (State (a+b) (u+v)) (State (a+b) (u+v)) ℚ)
    (hA : ∀ S T, A S T ≠ 0 → T.prefixCount a ≤ S.prefixCount a) (r : ℕ) :
    blockRestrict (A^r) = (blockRestrict A)^r := by
  induction r with
  | zero => exact blockRestrict_one a b u v
  | succ r ih =>
    rw [pow_succ,blockRestrict_mul _ _ (prefixCut_power A a hA r) hA,ih,pow_succ]

 theorem kronecker_power {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α α ℚ) (B : Matrix β β ℚ) (r : ℕ) :
    (A ⊗ₖ B)^r = (A^r) ⊗ₖ (B^r) := by
  induction r with
  | zero => simp only [pow_zero,Matrix.one_kronecker_one]
  | succ r ih => rw [pow_succ,ih,← Matrix.mul_kronecker_mul,← pow_succ,← pow_succ]

/-- The two-region track transport preserves actual boundary support. -/
theorem splitGlobalFilter_prefix (a b q : ℕ)
    (S T : State (blockWidth a+blockWidth b) q)
    (h : matrixCastTracks (blockWidth_add a b) (globalFilter (a+b) q) S T ≠ 0) :
    T.prefixCount (blockWidth a) ≤ S.prefixCount (blockWidth a) := by
  have hh := globalFilter_prefix_boundary
    (State.castTracks (blockWidth_add a b).symm S)
    (State.castTracks (blockWidth_add a b).symm T) h a
  simpa only [State.castTracks_prefix,blockWidth_eq] using hh

/-- Exact two-region diagonal block of every actual global-filter power. -/
theorem blockRestrict_globalFilter_power_split (a b u v r : ℕ) :
    blockRestrict (matrixCastTracks (blockWidth_add a b) ((globalFilter (a+b) (u+v))^r)) =
      ((globalFilter a u)^r) ⊗ₖ ((globalFilter b v)^r) := by
  rw [matrixCastTracks_pow,blockRestrict_power _ (splitGlobalFilter_prefix a b (u+v)),
    blockRestrict_globalFilter_split,kronecker_power]

/-- Increasing the number of blocks never decreases the chosen stabilizing exponent. -/
theorem globalProjectionExponent_mono {a b : ℕ} (h : a≤b) :
    globalProjectionExponent a ≤ globalProjectionExponent b := by
  unfold globalProjectionExponent
  exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h)
    (Nat.sub_le_sub_right h 1)) 2

 theorem globalProjectionExponent_large {a b : ℕ} (h : a≤b) :
    2*a*(a-1)+1 ≤ globalProjectionExponent b := by
  have hh := globalProjectionExponent_mono h
  unfold globalProjectionExponent at hh ⊢
  omega

@[simp] theorem globalFilter_power_castParticles {k q r : ℕ} (h : q=r)
    (S T : State (blockWidth k) q) (m : ℕ) :
    ((globalFilter k r)^m) (State.castParticles h S) (State.castParticles h T) =
      ((globalFilter k q)^m) S T := by subst r; rfl

/-- An actual state on two consecutive, half-filled groups of four-track blocks. -/
def splitState (a b : ℕ) (S : State (blockWidth a) (2*a) × State (blockWidth b) (2*b)) :
    State (blockWidth (a+b)) (2*(a+b)) :=
  State.castParticles (by omega)
    (State.castTracks (blockWidth_add a b).symm (State.join S.1 S.2))

/-- Restriction to the actual half-filled sectors of the two groups. -/
def splitRestrict (a b : ℕ)
    (M : Matrix (State (blockWidth (a+b)) (2*(a+b)))
      (State (blockWidth (a+b)) (2*(a+b))) ℚ) :
    Matrix (State (blockWidth a) (2*a) × State (blockWidth b) (2*b))
      (State (blockWidth a) (2*a) × State (blockWidth b) (2*b)) ℚ :=
  M.submatrix (splitState a b) (splitState a b)

/-- The larger projection restricts to the actual two smaller projections: all powers
are beyond both local stabilization thresholds. -/
theorem splitRestrict_projection (a b : ℕ) :
    splitRestrict a b (globalProjection (a+b)) = globalProjection a ⊗ₖ globalProjection b := by
  have h := blockRestrict_globalFilter_power_split a b (2*a) (2*b) (globalProjectionExponent (a+b))
  rw [globalFilter_power_eq_projection a _ (globalProjectionExponent_large (by omega)),
    globalFilter_power_eq_projection b _ (globalProjectionExponent_large (by omega))] at h
  ext S T
  have hh := congrFun (congrFun h S) T
  simpa only [splitRestrict,Matrix.submatrix_apply,splitState,globalProjection,
    globalFilter_power_castParticles,blockRestrict,matrixCastTracks] using hh

end HiddenCircuits
