import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Rank and trace of an actual finite idempotent matrix. -/
namespace HiddenCircuits
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The range of an idempotent is its fixed space, so its trace is the dimension of that range. -/
theorem idempotent_matrix_trace_eq_rank (A : Matrix ι ι K) (hA : A*A=A) :
    A.trace = (A.rank : K) := by
  have hi : IsIdempotentElem A.toLin' := by
    change A.toLin' * A.toLin' = A.toLin'
    rw [Module.End.mul_eq_comp,← Matrix.toLin'_mul,hA]
  have ht := (LinearMap.IsIdempotentElem.isProj_range A.toLin' hi).trace
  have hr : A.rank = Module.finrank K (LinearMap.range A.toLin') := by
    exact A.rank_eq_finrank_range_toLin (Pi.basisFun K ι) (Pi.basisFun K ι)
  rw [Matrix.trace_toLin'_eq,← hr] at ht
  exact ht

/-- Over characteristic zero, an explicit natural trace determines the rank exactly. -/
theorem idempotent_matrix_rank_of_trace [CharZero K] (A : Matrix ι ι K)
    (hA : A*A=A) (r : ℕ) (ht : A.trace = (r : K)) : A.rank = r := by
  apply Nat.cast_injective (R := K)
  exact (idempotent_matrix_trace_eq_rank A hA).symm.trans ht

end HiddenCircuits
