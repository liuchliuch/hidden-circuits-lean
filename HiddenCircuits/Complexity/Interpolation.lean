import HiddenCircuits.Complexity.SharpP
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.BigOperators

/-! Exact finite rational interpolation. Arithmetic identities here do not assert
an unproved machine running-time bound for rational arithmetic. -/
namespace HiddenCircuits.Complexity
open scoped BigOperators
open Polynomial

/-- The nonnegative consecutive nodes are the sizes of actual clone classes. -/
def interpolationNode {d : ℕ} (i : Fin (d+1)) : ℚ := i.val

theorem interpolationNode_injective (d : ℕ) :
    Function.Injective (@interpolationNode d) := by
  intro i j h
  apply Fin.ext
  unfold interpolationNode at h
  exact_mod_cast h

/-- The actual finite Lagrange expression applied to exact oracle values. -/
noncomputable def interpolateValues (d : ℕ) (values : Fin (d+1) → ℚ) : ℚ[X] :=
  Lagrange.interpolate Finset.univ interpolationNode values

theorem interpolateValues_correct (d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d) :
    interpolateValues d (fun i => p.eval (interpolationNode i)) = p := by
  apply Lagrange.interpolate_poly_eq_self
  · exact (interpolationNode_injective d).injOn
  · simp only [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)

/-- Recover a coefficient using exactly `d+1` exact values. -/
theorem coefficient_from_values (d : ℕ) (p : ℚ[X]) (hp : p.natDegree ≤ d) (k : ℕ) :
    (interpolateValues d (fun i => p.eval (interpolationNode i))).coeff k = p.coeff k := by
  rw [interpolateValues_correct d p hp]

/-- Grid recovery first substitutes `y=-1`, then extracts the requested x coefficient. -/
noncomputable def recoverGrid (dx dy k : ℕ)
    (values : Fin (dx+1) → Fin (dy+1) → ℚ) : ℚ :=
  (interpolateValues dx (fun i => (interpolateValues dy (values i)).eval (-1))).coeff k

/-- Generic two-parameter correctness. Its premises are polynomial identities and
degree bounds, not a source-hardness or runtime certificate. -/
theorem recoverGrid_correct (dx dy k : ℕ)
    (rows : ℚ → ℚ[X]) (column : ℚ[X])
    (hr : ∀ x, (rows x).natDegree ≤ dy)
    (hc : column.natDegree ≤ dx)
    (hcross : ∀ x, (rows x).eval (-1) = column.eval x) :
    recoverGrid dx dy k (fun i j => (rows (interpolationNode i)).eval (interpolationNode j)) =
      column.coeff k := by
  unfold recoverGrid
  simp_rw [interpolateValues_correct dy _ (hr _),hcross]
  rw [interpolateValues_correct dx column hc]

/-- The interpolation grid contains only polynomially many queries. -/
theorem interpolation_grid_card (dx dy : ℕ) :
    Fintype.card (Fin (dx+1) × Fin (dy+1)) = (dx+1)*(dy+1) := by simp

theorem interpolation_node_bound {d : ℕ} (i : Fin (d+1)) : i.val ≤ d := by omega

end HiddenCircuits.Complexity
