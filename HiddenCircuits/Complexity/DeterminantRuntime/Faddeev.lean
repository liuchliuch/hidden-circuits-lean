import HiddenCircuits.Complexity.DeterminantRuntime.AdjugateCoefficients

/-! A literal integer Faddeev–LeVerrier recurrence, exact division,
and equality of its signed final coefficient with the determinant. -/
namespace HiddenCircuits.Complexity.DeterminantRuntime
open Matrix Polynomial
variable {n : ℕ}

def nextCoefficient (A B : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : ℤ :=
  -(A * B).trace / (k + 1 : ℕ)

def faddeevStep (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ)
    (state : Matrix (Fin n) (Fin n) ℤ × ℤ) : Matrix (Fin n) (Fin n) ℤ × ℤ :=
  let c := nextCoefficient A state.1 k
  (A * state.1 + Matrix.scalar (Fin n) c, c)

def faddeevState (A : Matrix (Fin n) (Fin n) ℤ) : ℕ → Matrix (Fin n) (Fin n) ℤ × ℤ
  | 0 => (1, 1)
  | k + 1 => faddeevStep A k (faddeevState A k)

def determinant (A : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  (-1)^n * (faddeevState A n).2

noncomputable def adjState (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℤ := if k < n then adjCoeff A (n - (k + 1)) else 0

theorem trace_adj_round (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    -(A * adjState A k).trace = ((k + 1 : ℕ) : ℤ) * A.charpoly.coeff (n - (k + 1)) := by
  rw [adjState, if_pos hk, trace_mul_adjCoeff]
  have h : ((n - (k + 1) : ℕ) : ℤ) - n = -((k + 1 : ℕ) : ℤ) := by omega
  rw [h]
  ring

theorem nextCoefficient_adj (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    nextCoefficient A (adjState A k) k = A.charpoly.coeff (n - (k + 1)) := by
  rw [nextCoefficient, trace_adj_round A k hk]
  exact Int.mul_ediv_cancel_left _ (by omega)

theorem adjState_succ (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    A * adjState A k + Matrix.scalar (Fin n) (A.charpoly.coeff (n - (k + 1))) =
      adjState A (k + 1) := by
  rw [adjState, if_pos hk]
  by_cases hnext : k + 1 < n
  · rw [adjState, if_pos hnext]
    have h := adjCoeff_recurrence A (n - (k + 2))
    have he : n - (k + 2) + 1 = n - (k + 1) := by omega
    rw [he] at h
    rw [show k + 1 + 1 = k + 2 by omega, add_comm]
    exact (sub_eq_iff_eq_add.mp h).symm
  · rw [adjState, if_neg hnext]
    have he : n - (k + 1) = 0 := by omega
    rw [he, ← adjCoeff_constant]
    exact add_neg_cancel _

theorem adjState_zero (A : Matrix (Fin n) (Fin n) ℤ) : adjState A 0 = 1 := by
  by_cases hn : 0 < n
  · simpa [adjState, hn] using adjCoeff_leading A hn
  · have he : n = 0 := by omega
    subst n
    ext i j
    exact Fin.elim0 i

theorem charpoly_coeff_top (A : Matrix (Fin n) (Fin n) ℤ) : A.charpoly.coeff n = 1 := by
  simpa [Polynomial.leadingCoeff] using A.charpoly_monic.leadingCoeff

theorem faddeevState_correct (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k ≤ n) :
    faddeevState A k = (adjState A k, A.charpoly.coeff (n - k)) := by
  induction k with
  | zero => simp [faddeevState, adjState_zero, charpoly_coeff_top]
  | succ k ih =>
    have hkn : k < n := by omega
    rw [faddeevState, ih (by omega), faddeevStep]
    simp only [nextCoefficient_adj A k hkn, adjState_succ A k hkn]

theorem faddeevState_divisible (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    ((k + 1 : ℕ) : ℤ) ∣ -(A * (faddeevState A k).1).trace := by
  rw [faddeevState_correct A k (by omega)]
  exact ⟨A.charpoly.coeff (n - (k + 1)), trace_adj_round A k hk⟩

theorem determinant_eq_det (A : Matrix (Fin n) (Fin n) ℤ) : determinant A = A.det := by
  rw [determinant, faddeevState_correct A n (le_refl n)]
  simpa using (Matrix.det_eq_sign_charpoly_coeff A).symm

end HiddenCircuits.Complexity.DeterminantRuntime
