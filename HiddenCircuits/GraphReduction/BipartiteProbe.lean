import HiddenCircuits.GraphReduction.ProbePolynomial
import HiddenCircuits.GraphReduction.WeightedExpansion
import HiddenCircuits.Complexity.Interpolation

/-! The full bipartite probe cancellation identity and its finite actual graph queries. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators
open Polynomial
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

/-- Lemma 9.2's negative evaluation is the weighted count of actual original perfect matchings. -/
theorem bipartiteProbe_cancellation (R : X → Y → Prop)
    (A : I → X → Prop) (B : I → Y → Prop) :
    (probePolynomial R A B).eval (-1) = weightedBipartiteCount (probeWeight R A B) := by
  rw [probePolynomial_neg_one,weightedBipartiteCount_blocks]

 theorem probePolynomial_degree_right (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    (probePolynomial R A B).natDegree ≤ Fintype.card Y := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro cd _
  apply (natDegree_C_mul_le _ _).trans
  apply (natDegree_prod_le ..).trans
  simp only [descPochhammer_natDegree]
  calc
    ∑ i, Fintype.card (OriginalFiber cd.val.val.1 (some i)) =
        ∑ i, Fintype.card (OriginalFiber cd.val.val.2 (some i)) :=
      Finset.sum_congr rfl (fun i _ => cd.property i)
    _ ≤ Fintype.card Y := assigned_card_le cd.val.val.2

/-- The paper's degree bound uses all original vertices, without equal-part-size assumptions. -/
theorem bipartiteProbe_degree (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    (probePolynomial R A B).natDegree ≤ (Fintype.card X+Fintype.card Y)/2 := by
  have hX := probePolynomial_degree R A B
  have hY := probePolynomial_degree_right R A B
  omega

/-- Full Section 9 bipartite probe lemma: arbitrary overlaps, every natural sample,
and the exact negatively weighted original matching count. -/
theorem bipartiteProbe_identity (R : X → Y → Prop)
    (A : I → X → Prop) (B : I → Y → Prop) :
    ∃ Φ : ℚ[X], Φ.natDegree ≤ (Fintype.card X+Fintype.card Y)/2 ∧
      (∀ s : ℕ, Φ.eval (s : ℚ) = (perfectMatchingCount (probeGraph R A B s) : ℚ) /
        (s.factorial : ℚ)^Fintype.card I) ∧
      Φ.eval (-1)=weightedBipartiteCount (probeWeight R A B) :=
  ⟨probePolynomial R A B,bipartiteProbe_degree R A B,probePolynomial_count R A B,
    bipartiteProbe_cancellation R A B⟩

/-- Explicit Lagrange recovery from the actual simple-unweighted query counts. -/
noncomputable def recoverProbeCount (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) : ℚ :=
  (Complexity.interpolateValues ((Fintype.card X+Fintype.card Y)/2)
    (fun i => (perfectMatchingCount (probeGraph R A B i.val) : ℚ) /
      (i.val.factorial : ℚ)^Fintype.card I)).eval (-1)

 theorem recoverProbeCount_correct (R : X → Y → Prop) (A : I → X → Prop) (B : I → Y → Prop) :
    recoverProbeCount R A B = weightedBipartiteCount (probeWeight R A B) := by
  unfold recoverProbeCount
  have hn : (fun i : Fin ((Fintype.card X+Fintype.card Y)/2+1) =>
      (perfectMatchingCount (probeGraph R A B i.val) : ℚ)/(i.val.factorial : ℚ)^Fintype.card I) =
      (fun i => (probePolynomial R A B).eval (Complexity.interpolationNode i)) := by
    funext i
    exact (probePolynomial_count R A B i.val).symm
  rw [hn,Complexity.interpolateValues_correct _ _ (bipartiteProbe_degree R A B),
    bipartiteProbe_cancellation]

 theorem bipartiteProbe_query_count :
    Fintype.card (Fin ((Fintype.card X+Fintype.card Y)/2+1)) =
      (Fintype.card X+Fintype.card Y)/2+1 := Fintype.card_fin _

 theorem bipartiteProbe_query_size (s : Fin ((Fintype.card X+Fintype.card Y)/2+1)) :
    Fintype.card (ProbePart X I s.val ⊕ ProbePart Y I s.val) ≤
      Fintype.card X+Fintype.card Y+2*Fintype.card I*((Fintype.card X+Fintype.card Y)/2) := by
  rw [probeGraph_card]
  have hs : s.val ≤ (Fintype.card X+Fintype.card Y)/2 := by omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _

end HiddenCircuits.GraphReduction
