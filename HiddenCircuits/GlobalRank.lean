import HiddenCircuits.GlobalStabilization
import HiddenCircuits.TracePotential
import HiddenCircuits.ProjectionRank

namespace HiddenCircuits
open scoped Kronecker BigOperators

/-- Equal-potential entries of the concrete global word are exactly its balanced diagonal part. -/
theorem globalFilter_eq_diagonal_of_potential_eq {k : ℕ}
    (S T : State (blockWidth k) (2*k)) (he : S.boundaryPotential=T.boundaryPotential) :
    globalFilter k (2*k) S T = globalDiagonal k S T := by
  by_cases hf : globalFilter k (2*k) S T=0
  · by_cases hd : globalDiagonal k S T=0
    · rw [hf,hd]
    · have hb := globalDiagonal_support S T hd
      exact (globalDiagonal_eq_filter S T hb.1 hb.2).symm
  · have hc := (globalFilter_potential_eq_iff_all S T hf).mp he
    have hb := globalFilter_sameCounts_balanced k S T hc hf
    exact (globalDiagonal_eq_filter S T hb.1 hb.2).symm

 theorem localFilter_trace : (localFilter 2).trace=2 := by
  have h := idempotent_matrix_trace_eq_rank (localFilter 2) localFilter_idempotent
  rw [localFilter_rank] at h
  exact h

 theorem balancedTensor_trace (k : ℕ) : (balancedTensor k).trace=(2:ℚ)^k := by
  induction k with
  | zero =>
    change (1 : Matrix PUnit PUnit ℚ).trace = 1
    simp
  | succ k ih =>
    change (localFilter 2 ⊗ₖ balancedTensor k).trace = (2:ℚ)^(k+1)
    rw [Matrix.trace_kronecker,localFilter_trace,ih,pow_succ']

 theorem globalDiagonal_trace (k : ℕ) : (globalDiagonal k).trace=(2:ℚ)^k := by
  rw [globalDiagonal,embedMatrix_trace _ (balancedJoin_injective k),balancedTensor_trace]

/-- Closed paths cannot use any strict-flow edge, so all positive powers have the same trace. -/
theorem globalFilter_power_trace (k m : ℕ) (hm : 0<m) :
    ((globalFilter k (2*k))^m).trace = (2:ℚ)^k := by
  rw [potential_pow_trace (globalFilter k (2*k)) (globalDiagonal k) State.boundaryPotential
    (fun S T => globalFilter_potential_le S T)
    (fun S T h => (globalDiagonal_potential_eq S T h).le)
    (fun S T => globalFilter_eq_diagonal_of_potential_eq S T)]
  have hp : (globalDiagonal k)^m = globalDiagonal k := by
    have hstep : (globalDiagonal k)^(1+1) = (globalDiagonal k)^1 := by
      simpa only [show (1:ℕ)+1=2 by rfl,pow_two,pow_one] using globalDiagonal_idempotent k
    simpa only [pow_one] using powers_eq_after hstep m (by omega)
  rw [hp,globalDiagonal_trace]

 theorem globalProjection_trace (k : ℕ) : (globalProjection k).trace = (2:ℚ)^k :=
  globalFilter_power_trace k (globalProjectionExponent k) (by unfold globalProjectionExponent; omega)

/-- Proposition 5.2: rank of the actual polynomial power of the literal global filter word. -/
theorem globalProjection_rank (k : ℕ) : (globalProjection k).rank = 2^k := by
  apply idempotent_matrix_rank_of_trace _ (globalProjection_idempotent k)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using globalProjection_trace k

/-- Both mathematical conclusions of Proposition 5.2, with no assumed locality or projection certificate. -/
theorem globalProjection_idempotent_rank (k : ℕ) :
    globalProjection k * globalProjection k = globalProjection k ∧ (globalProjection k).rank=2^k :=
  ⟨globalProjection_idempotent k,globalProjection_rank k⟩

end HiddenCircuits
