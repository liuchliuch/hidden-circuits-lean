import HiddenCircuits.GlobalDiagonal
import HiddenCircuits.GlobalFlow
import HiddenCircuits.Stabilization

/-! Stabilization and idempotence of the actual global filter power, with the
paper's explicit polynomial exponent. -/
namespace HiddenCircuits
open scoped BigOperators

/-- All balanced states have the same boundary potential. -/
theorem balanced_potential_eq {k : ℕ} (S T : State (blockWidth k) (2*k))
    (hS : Balanced S) (hT : Balanced T) : S.boundaryPotential = T.boundaryPotential := by
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val+1 ≤ k := by have hh := j.isLt; omega
  rw [hS (j.val+1) hj,hT (j.val+1) hj]

/-- Every actual diagonal-sector transition preserves the boundary potential. -/
theorem globalDiagonal_potential_eq {k : ℕ} (S T : State (blockWidth k) (2*k))
    (h : globalDiagonal k S T ≠ 0) : S.boundaryPotential = T.boundaryPotential := by
  have hb := globalDiagonal_support S T h
  exact balanced_potential_eq S T hb.1 hb.2

/-- Every nonzero entry remaining after removing the balanced diagonal strictly
advances the concrete bounded potential. -/
theorem globalOffDiagonal_potential_strict {k : ℕ} (S T : State (blockWidth k) (2*k))
    (h : globalOffDiagonal k S T ≠ 0) : S.boundaryPotential+1 ≤ T.boundaryPotential :=
  globalFilter_potential_strict_of_prefix_ne S T
    (globalOffDiagonal_filter_nonzero S T h) (globalOffDiagonal_counts_ne S T h)

/-- Powers of the actual off-diagonal part record at least one unit of flow per factor. -/
theorem globalOffDiagonal_power_support (k a : ℕ) (S T : State (blockWidth k) (2*k))
    (h : ((globalOffDiagonal k)^a) S T ≠ 0) :
    S.boundaryPotential+a ≤ T.boundaryPotential :=
  potential_pow_support (globalOffDiagonal k) State.boundaryPotential
    (fun S T => globalOffDiagonal_potential_strict S T) a S T h

/-- A positive run of strict flow cannot leave the balanced sector and return. -/
theorem globalDiagonal_separated (k a : ℕ) (ha : 0<a) :
    globalDiagonal k * (globalOffDiagonal k)^a * globalDiagonal k = 0 := by
  ext S T
  by_contra hn
  rw [Matrix.mul_apply] at hn
  obtain ⟨U,_,hU⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hDU : (globalDiagonal k * (globalOffDiagonal k)^a) S U ≠ 0 :=
    fun hz => hU (by rw [hz,zero_mul])
  have hDT : globalDiagonal k U T ≠ 0 := fun hz => hU (by rw [hz,mul_zero])
  rw [Matrix.mul_apply] at hDU
  obtain ⟨V,_,hV⟩ := Finset.exists_ne_zero_of_sum_ne_zero hDU
  have hDS : globalDiagonal k S V ≠ 0 := fun hz => hV (by rw [hz,zero_mul])
  have hN : ((globalOffDiagonal k)^a) V U ≠ 0 := fun hz => hV (by rw [hz,mul_zero])
  have he := balanced_potential_eq V U (globalDiagonal_support S V hDS).2
    (globalDiagonal_support U T hDT).1
  have hs := globalOffDiagonal_power_support k a V U hN
  omega

/-- The decomposition uses the globally defined filter itself. -/
theorem globalFilter_decomposition (k : ℕ) :
    globalDiagonal k + globalOffDiagonal k = globalFilter k (2*k) := by
  unfold globalOffDiagonal
  abel

/-- The concrete off-diagonal part is nilpotent in polynomially bounded degree. -/
theorem globalOffDiagonal_nilpotent (k : ℕ) :
    (globalOffDiagonal k)^(2*k*(k-1)+1) = 0 := by
  apply potential_nilpotent (globalOffDiagonal k) State.boundaryPotential 0 (2*k*(k-1))
    (fun S T => globalOffDiagonal_potential_strict S T)
    (fun S => Nat.zero_le _)
  intro S
  simpa only [zero_add] using S.boundaryPotential_upper

/-- The actual filter powers stabilize after at most `2*k*(k-1)+1` factors.
Every structural condition is proved for the concrete diagonal/off-diagonal split. -/
theorem globalFilter_stabilization (k : ℕ) :
    (∀ m, 2*k*(k-1)+1 ≤ m →
      (globalFilter k (2*k))^m = (globalFilter k (2*k))^(2*k*(k-1)+1)) ∧
    (globalFilter k (2*k))^(2*k*(k-1)+2) *
      (globalFilter k (2*k))^(2*k*(k-1)+2) =
      (globalFilter k (2*k))^(2*k*(k-1)+2) := by
  have hh := bounded_flow_stabilizes (globalDiagonal k) (globalOffDiagonal k)
    State.boundaryPotential 0 (2*k*(k-1)) (globalDiagonal_idempotent k)
    (fun a ha => globalDiagonal_separated k a ha)
    (fun S T => globalOffDiagonal_potential_strict S T)
    (fun S T h => (globalDiagonal_potential_eq S T h).le)
    (fun S => Nat.zero_le _)
    (fun S => by simpa only [zero_add] using S.boundaryPotential_upper)
  simpa only [globalFilter_decomposition] using hh

/-- The exact exponent `K_k` specified in Section 5. -/
def globalProjectionExponent (k : ℕ) : ℕ := 2*k*(k-1)+2

/-- The paper's concrete global encoding projection, without a certificate hypothesis. -/
def globalProjection (k : ℕ) :
    Matrix (State (blockWidth k) (2*k)) (State (blockWidth k) (2*k)) ℚ :=
  (globalFilter k (2*k))^(globalProjectionExponent k)

/-- Idempotence of the actual power at the paper's exact polynomial exponent. -/
theorem globalProjection_idempotent (k : ℕ) :
    globalProjection k * globalProjection k = globalProjection k :=
  (globalFilter_stabilization k).2

/-- Every sufficiently late actual filter power is the same concrete projection. -/
theorem globalFilter_power_eq_projection (k m : ℕ) (hm : 2*k*(k-1)+1 ≤ m) :
    (globalFilter k (2*k))^m = globalProjection k := by
  have hs := (globalFilter_stabilization k).1
  exact (hs m hm).trans (hs (globalProjectionExponent k)
    (by unfold globalProjectionExponent; omega)).symm

 theorem globalFilter_mul_projection (k : ℕ) :
    globalFilter k (2*k) * globalProjection k = globalProjection k := by
  unfold globalProjection
  rw [← pow_succ']
  exact globalFilter_power_eq_projection k (globalProjectionExponent k+1)
    (by unfold globalProjectionExponent; omega)

 theorem globalProjection_mul_filter (k : ℕ) :
    globalProjection k * globalFilter k (2*k) = globalProjection k := by
  unfold globalProjection
  rw [← pow_succ]
  exact globalFilter_power_eq_projection k (globalProjectionExponent k+1)
    (by unfold globalProjectionExponent; omega)

end HiddenCircuits
