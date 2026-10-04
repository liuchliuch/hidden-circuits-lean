import HiddenCircuits.GraphReduction.CliqueProbePolynomial
import HiddenCircuits.Complexity.Interpolation

/-! Exact even-node interpolation of actual unweighted clique-probe query counts. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
open Polynomial

/-- The literal even sample sizes 0,2,...,2d, viewed as rational interpolation nodes. -/
def cliqueInterpolationNode {d : ℕ} (i : Fin (d+1)) : ℚ := 2*i.val

 theorem cliqueInterpolationNode_injective (d : ℕ) : Function.Injective (@cliqueInterpolationNode d) := by
  intro i j h
  apply Fin.ext
  unfold cliqueInterpolationNode at h
  have hq : (i.val : ℚ)=(j.val : ℚ) := by linarith
  exact_mod_cast hq

noncomputable def interpolateCliqueValues (d : ℕ) (values : Fin (d+1) → ℚ) : ℚ[X] :=
  Lagrange.interpolate Finset.univ cliqueInterpolationNode values

 theorem interpolateCliqueValues_correct (d : ℕ) (p : ℚ[X]) (hp : p.natDegree≤d) :
    interpolateCliqueValues d (fun i => p.eval (cliqueInterpolationNode i))=p := by
  apply Lagrange.interpolate_poly_eq_self
  · exact (cliqueInterpolationNode_injective d).injOn
  · simp only [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)

variable {V I : Type*} [Fintype V] [Fintype I]

/-- Query only simple unweighted graphs at nonnegative even sizes, normalize, interpolate. -/
noncomputable def recoverCliqueProbe (G : SimpleGraph V) (A : I → V → Prop) : ℚ :=
  (interpolateCliqueValues (Fintype.card V/2)
    (fun i => (perfectMatchingCount (cliqueProbeGraph G A (2*i.val)) : ℚ) /
      (oddFactorial i.val : ℚ)^Fintype.card I)).eval (-1)

 theorem recoverCliqueProbe_polynomial (G : SimpleGraph V) (A : I → V → Prop) :
    recoverCliqueProbe G A=(cliqueProbePolynomial G A).eval (-1) := by
  have hn : (fun i : Fin (Fintype.card V/2+1) =>
      (perfectMatchingCount (cliqueProbeGraph G A (2*i.val)) : ℚ) /
        (oddFactorial i.val : ℚ)^Fintype.card I) =
      (fun i => (cliqueProbePolynomial G A).eval (cliqueInterpolationNode i)) := by
    funext i
    exact (cliqueProbePolynomial_count G A i.val).symm
  unfold recoverCliqueProbe
  rw [hn,interpolateCliqueValues_correct _ _ (cliqueProbePolynomial_degree G A)]

 theorem cliqueProbe_query_count : Fintype.card (Fin (Fintype.card V/2+1))=Fintype.card V/2+1 :=
  Fintype.card_fin _

/-- Every even sample is at most the original graph size. -/
theorem cliqueProbe_sample_size (i : Fin (Fintype.card V/2+1)) : 2*i.val≤Fintype.card V := by
  have hi := i.isLt
  omega

/-- The actual expanded graph has at most n₀(b+1) vertices. -/
theorem cliqueProbe_query_size (i : Fin (Fintype.card V/2+1)) :
    Fintype.card (V ⊕ (I × Fin (2*i.val))) ≤ Fintype.card V*(Fintype.card I+1) := by
  rw [cliqueProbeGraph_card]
  calc
    Fintype.card V+Fintype.card I*(2*i.val) ≤
        Fintype.card V+Fintype.card I*Fintype.card V :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (cliqueProbe_sample_size i)) _
    _ = _ := by ring

end HiddenCircuits.GraphReduction
