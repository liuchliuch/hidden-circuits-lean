import HiddenCircuits.GraphReduction.Runtime.WordGraph.MonotonePermutationWordSolver
import HiddenCircuits.GraphReduction.Runtime.SuppliedMembership
import HiddenCircuits.GraphReduction.NaturalOrderedClasses
import HiddenCircuits.Complexity.FPCollapse

/-! Machine-grounded matching hardness with a supplied two-line permutation
representation of a monotone (equivalently, bipartite permutation) graph.
The program emits the adjacency matrix and both compressed endpoint vectors;
it does not substitute native row-neighborhood arrays for a diagram packet. -/
namespace HiddenCircuits.GraphReduction
open Complexity Runtime Runtime.WordGraph

/-- The same graph and its genuine injective two-line diagram are supplied.
Only the natural monotone graph promise is assumed of the counting oracle. -/
def SuppliedMonotonePermutationOracle (g : BitString → ℕ) : Prop :=
  ∀ (G : GraphInput) (D : PermutationDiagram (Fin G.1)),
    D.graph = G.2.graph → MonotoneGraph G.2.graph →
    g (suppliedPermutationBits G D) = perfectMatchingCount G.2.graph

/-- Equivalent whole-class promise, expressed using bipartite permutation graphs. -/
def SuppliedBipartitePermutationOracle (g : BitString → ℕ) : Prop :=
  ∀ (G : GraphInput) (D : PermutationDiagram (Fin G.1)),
    D.graph = G.2.graph → BipartitePermutationGraph G.2.graph →
    g (suppliedPermutationBits G D) = perfectMatchingCount G.2.graph

lemma suppliedMonotone_iff_bipartitePermutation (g : BitString → ℕ) :
    SuppliedMonotonePermutationOracle g ↔ SuppliedBipartitePermutationOracle g := by
  constructor
  · intro h G D hD hG
    exact h G D hD hG.monotone
  · intro h G D hD hG
    exact h G D hD hG.bipartitePermutation

lemma monotonePermutation_queryBits (w : WordInstance) (t s : ℕ) :
    MonotonePermutationAnswer.queryBits w t s =
      suppliedPermutationBits (MonotonePermutationWordQuery.graphInput w t s)
        (monotoneMatrixDiagram (fun i => (sampleWord w.word t).get i) w.source w.target s) := rfl

lemma suppliedMonotone_wordSolverSpec (g : BitString → ℕ)
    (hg : SuppliedMonotonePermutationOracle g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec MonotonePermutationDriver.program g
      MonotonePermutationDriver.time := by
  intro w
  apply MonotonePermutationDriver.program_executes g w
  intro _ q
  change g (MonotonePermutationAnswer.queryBits w q.1.val q.2.val) = _
  rw [monotonePermutation_queryBits]
  exact hg _ _ (monotoneMatrixDiagram_graph _ _ _ _) (monotoneGraphInput_monotone _ _ _ _)

/-- The concrete physical supplied-diagram reducer witnesses #P hardness;
there is no compiler, runtime, or source-hardness hypothesis. -/
theorem suppliedMonotone_matching_sharpPHard (g : BitString → ℕ)
    (hg : SuppliedMonotonePermutationOracle g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard MonotonePermutationDriver.program g
    MonotonePermutationDriver.time (suppliedMonotone_wordSolverSpec g hg)

theorem suppliedBipartitePermutation_matching_sharpPHard (g : BitString → ℕ)
    (hg : SuppliedBipartitePermutationOracle g) : SharpPHard g :=
  suppliedMonotone_matching_sharpPHard g ((suppliedMonotone_iff_bipartitePermutation g).mpr hg)

/-- Total #P extension: count the physically projected graph field. As with
other supplied-representation promises, representation bytes are not validated
off promise. This is not a zero-on-invalid-diagram claim. -/
noncomputable def suppliedMonotoneGraphFieldProblem : BitString → ℕ :=
  suppliedPrivateGraphFieldProblem

lemma suppliedMonotoneGraphFieldProblem_oracle :
    SuppliedMonotonePermutationOracle suppliedMonotoneGraphFieldProblem := by
  intro G D _ _
  simp only [suppliedMonotoneGraphFieldProblem,suppliedPrivateGraphFieldProblem,
    Function.comp_apply,suppliedPrivate_graphField,GraphInput.perfectMatchingProblem,
    GraphInput.decode_encode]

theorem suppliedMonotoneGraphFieldProblem_sharpP : SharpP suppliedMonotoneGraphFieldProblem :=
  suppliedPrivateGraphFieldProblem_sharpP

theorem suppliedMonotoneGraphFieldProblem_sharpPHard : SharpPHard suppliedMonotoneGraphFieldProblem :=
  suppliedMonotone_matching_sharpPHard _ suppliedMonotoneGraphFieldProblem_oracle

theorem suppliedMonotone_has_sharpP_complete_extension :
    ∃ f : BitString → ℕ, SharpP f ∧ SharpPHard f ∧ SuppliedMonotonePermutationOracle f :=
  ⟨suppliedMonotoneGraphFieldProblem,suppliedMonotoneGraphFieldProblem_sharpP,
    suppliedMonotoneGraphFieldProblem_sharpPHard,suppliedMonotoneGraphFieldProblem_oracle⟩

theorem suppliedBipartitePermutation_has_sharpP_complete_extension :
    ∃ f : BitString → ℕ, SharpP f ∧ SharpPHard f ∧ SuppliedBipartitePermutationOracle f :=
  ⟨suppliedMonotoneGraphFieldProblem,suppliedMonotoneGraphFieldProblem_sharpP,
    suppliedMonotoneGraphFieldProblem_sharpPHard,
    (suppliedMonotone_iff_bipartitePermutation _).mp suppliedMonotoneGraphFieldProblem_oracle⟩
/-- An unrestricted polynomial-time exact supplied-diagram oracle collapses
literal natural-valued FP and #P. -/
theorem suppliedMonotone_matching_fp_collapse {g : BitString → ℕ}
    (hg : SuppliedMonotonePermutationOracle g) (hfp : FP g) : FP_eq_SharpP :=
  (suppliedMonotone_matching_sharpPHard g hg).fp_eq_sharpP hfp

theorem suppliedBipartitePermutation_matching_fp_collapse {g : BitString → ℕ}
    (hg : SuppliedBipartitePermutationOracle g) (hfp : FP g) : FP_eq_SharpP :=
  (suppliedBipartitePermutation_matching_sharpPHard g hg).fp_eq_sharpP hfp
end HiddenCircuits.GraphReduction
