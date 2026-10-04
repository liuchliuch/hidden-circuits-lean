import HiddenCircuits.Circuit.SpectralNodes
import HiddenCircuits.Circuit.PathExpansion

namespace HiddenCircuits.Circuit
open scoped BigOperators
open Polynomial
noncomputable section

/-- The genuinely distinct integer spectral nodes, viewed as exact rational interpolation nodes. -/
def rationalSpectralNode {g : ℕ} (x : SpectralIndex g) : ℚ := spectralNode x.1.val x.2.val

 theorem rationalSpectralNode_injective (g : ℕ) : Function.Injective (@rationalSpectralNode g) := by
  intro x y h
  apply spectralPair_injective g
  apply spectralNode_injective
  change (spectralNode x.1.val x.2.val : ℚ)=(spectralNode y.1.val y.2.val : ℚ) at h
  change spectralNode x.1.val x.2.val=spectralNode y.1.val y.2.val
  exact_mod_cast h

 theorem spectralIndex_card_pos (g : ℕ) : 0<Fintype.card (SpectralIndex g) := by
  let x : SpectralIndex g := ⟨⟨0,by omega⟩,⟨0,by omega⟩⟩
  exact Fintype.card_pos_iff.mpr ⟨x⟩

/-- The actual finite interpolating polynomial prescribed in Lemma7.2. -/
def spectralPolynomial (g : ℕ) (target : SpectralIndex g → ℚ) : ℚ[X] :=
  Lagrange.interpolate Finset.univ rationalSpectralNode target

 theorem spectralPolynomial_at_node (g : ℕ) (target : SpectralIndex g → ℚ) (x : SpectralIndex g) :
    (spectralPolynomial g target).eval (rationalSpectralNode x)=target x := by
  exact Lagrange.eval_interpolate_at_node _ ((rationalSpectralNode_injective g).injOn) (Finset.mem_univ x)

 theorem spectralPolynomial_degree (g : ℕ) (target : SpectralIndex g → ℚ) :
    (spectralPolynomial g target).natDegree<Fintype.card (SpectralIndex g) := by
  by_cases hz:spectralPolynomial g target=0
  · simpa [hz] using spectralIndex_card_pos g
  · apply (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
    simpa only [Finset.card_univ] using
      Lagrange.degree_interpolate_lt target ((rationalSpectralNode_injective g).injOn)

/-- Coefficients of the actual interpolation polynomial. -/
def spectralCoefficient (g : ℕ) (target : SpectralIndex g → ℚ) (r : ℕ) : ℚ :=
  (spectralPolynomial g target).coeff r

 theorem spectralCoefficients_node (g : ℕ) (target : SpectralIndex g → ℚ) (x : SpectralIndex g) :
    (∑ r ∈ Finset.range (Fintype.card (SpectralIndex g)),
      spectralCoefficient g target r * rationalSpectralNode x ^ r)=target x := by
  unfold spectralCoefficient
  rw [← Polynomial.eval_eq_sum_range' (spectralPolynomial_degree g target),spectralPolynomial_at_node]

/-- Products of N diagonal entries: only paths with no11 occurrence survive. -/
def forbidTarget {g : ℕ} (x : SpectralIndex g) : ℚ := if x.1.val+x.2.val=g then 1 else 0

/-- Products of CZ diagonal entries: every11 occurrence contributes its exact sign. -/
def controlledSignTarget {g : ℕ} (x : SpectralIndex g) : ℚ := (-1:ℚ)^(g-x.1.val-x.2.val)

/-- A power sample sums actual class coefficients against the shared α_ab^r. -/
def spectralMoment {g : ℕ} (c : SpectralIndex g → ℚ) (r : ℕ) : ℚ :=
  ∑ x, c x * rationalSpectralNode x ^ r

/-- All marked occurrences of one type are recovered simultaneously, with only J_g samples. -/
theorem spectral_moment_recovery (g : ℕ) (target c : SpectralIndex g → ℚ) :
    (∑ r ∈ Finset.range (Fintype.card (SpectralIndex g)),
      spectralCoefficient g target r * spectralMoment c r) = ∑ x, c x * target x := by
  unfold spectralMoment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have h : (∑ r ∈ Finset.range (Fintype.card (SpectralIndex g)),
      spectralCoefficient g target r * (c x*rationalSpectralNode x^r)) =
      c x * ∑ r ∈ Finset.range (Fintype.card (SpectralIndex g)),
        spectralCoefficient g target r*rationalSpectralNode x^r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [h,spectralCoefficients_node]

/-- Regrouped finite path coefficients produce exactly the same recovery; no circuit adjacency
or gate-order restriction is imposed on the path family. -/
theorem spectral_path_recovery {α : Type*} [Fintype α] (g : ℕ)
    (classes : α → SpectralIndex g) (weight : α → ℚ) (target : SpectralIndex g → ℚ) :
    (∑ r ∈ Finset.range (Fintype.card (SpectralIndex g)),
      spectralCoefficient g target r * ∑ a, weight a*rationalSpectralNode (classes a)^r) =
      ∑ a, weight a*target (classes a) := by
  let c : SpectralIndex g → ℚ := fun x => ∑ a, if classes a=x then weight a else 0
  have hs (r : ℕ) : (∑ a, weight a*rationalSpectralNode (classes a)^r)=spectralMoment c r :=
    sum_group_factor classes weight (fun x => rationalSpectralNode x^r)
  simp_rw [hs]
  rw [sum_group_factor classes weight target]
  exact spectral_moment_recovery g target c

end
end HiddenCircuits.Circuit
