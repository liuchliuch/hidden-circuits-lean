import HiddenCircuits.BalancedSector
import HiddenCircuits.MatrixEmbedding

namespace HiddenCircuits

/-- The balanced diagonal block extended by zero to the full actual subset state space. -/
def globalDiagonal (k : ℕ) : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ :=
  embedMatrix (balancedJoin k) (balancedTensor k)

/-- The actual remaining transitions after removing the balanced diagonal sector. -/
def globalOffDiagonal (k : ℕ) : Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ :=
  globalFilter k (2*k) - globalDiagonal k

 theorem globalDiagonal_idempotent (k : ℕ) : globalDiagonal k * globalDiagonal k = globalDiagonal k :=
  embedMatrix_idempotent _ (balancedJoin_injective k) _ (balancedTensor_idempotent k)

 theorem globalDiagonal_support {k : ℕ} (S T : State (blockWidth k) (2*k))
    (h : globalDiagonal k S T ≠ 0) : Balanced S ∧ Balanced T := by
  obtain ⟨⟨s,rfl⟩,⟨t,rfl⟩⟩ := embedMatrix_nonzero _ _ S T h
  exact ⟨balancedJoin_balanced k s,balancedJoin_balanced k t⟩

 theorem globalDiagonal_eq_filter {k : ℕ} (S T : State (blockWidth k) (2*k))
    (hS : Balanced S) (hT : Balanced T) : globalDiagonal k S T = globalFilter k (2*k) S T := by
  obtain ⟨s,rfl⟩ := balancedJoin_surjective k S hS
  obtain ⟨t,rfl⟩ := balancedJoin_surjective k T hT
  rw [globalDiagonal,embedMatrix_apply _ (balancedJoin_injective k)]
  exact (congrFun (congrFun (balancedTensor_eq_restrict k) s) t).symm

/-- The off-diagonal part cannot contain a balanced-to-balanced transition. -/
theorem globalOffDiagonal_zero_balanced {k : ℕ} (S T : State (blockWidth k) (2*k))
    (hS : Balanced S) (hT : Balanced T) : globalOffDiagonal k S T = 0 := by
  simp only [globalOffDiagonal,Matrix.sub_apply,globalDiagonal_eq_filter S T hS hT,sub_self]

/-- A nonzero remaining transition is genuinely in the original global word. -/
theorem globalOffDiagonal_filter_nonzero {k : ℕ} (S T : State (blockWidth k) (2*k))
    (h : globalOffDiagonal k S T ≠ 0) : globalFilter k (2*k) S T ≠ 0 := by
  by_cases hd : globalDiagonal k S T=0
  · simpa only [globalOffDiagonal,Matrix.sub_apply,hd,sub_zero] using h
  · have hb := globalDiagonal_support S T hd
    exact False.elim (h (globalOffDiagonal_zero_balanced S T hb.1 hb.2))

/-- Every remaining nonzero transition changes the count vector strictly. -/
theorem globalOffDiagonal_counts_ne {k : ℕ} (S T : State (blockWidth k) (2*k))
    (h : globalOffDiagonal k S T ≠ 0) : ¬ SameBlockCounts S T := by
  intro he
  have hb := globalFilter_sameCounts_balanced k S T he (globalOffDiagonal_filter_nonzero S T h)
  exact h (globalOffDiagonal_zero_balanced S T hb.1 hb.2)

end HiddenCircuits
