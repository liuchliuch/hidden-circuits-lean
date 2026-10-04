import HiddenCircuits.GraphReduction.Runtime.CliqueGraphHardness

/-! Retained supplied-diagram hardness section; graph-only statements are
imported without semantic changes from CliqueGraphHardness. -/
namespace HiddenCircuits.GraphReduction
open Complexity
open Runtime.WordGraph

/-- The supplied diagram consists of its two finite integer endpoint vectors;
the graph is carried explicitly as a redundant adjacency-matrix component. -/
def suppliedPermutationBits (G : GraphInput) (D : PermutationDiagram (Fin G.1)) : BitString :=
  encodeBitList [G.encode,
    encodeBitList (List.ofFn (fun i => List.replicate (D.upper i) true)),
    encodeBitList (List.ofFn (fun i => List.replicate (D.lower i) true))]
def SuppliedChordalPermutationOracle (g : BitString → ℕ) : Prop :=
  ∀ (G : GraphInput) (D : PermutationDiagram (Fin G.1)),D.graph=G.2.graph → Chordal G.2.graph →
    g (suppliedPermutationBits G D)=perfectMatchingCount G.2.graph

lemma suppliedPrivate_wordSolverSpec (g : BitString → ℕ) (hg : SuppliedChordalPermutationOracle g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec (CliqueDriver.program .suppliedPrivate) g (CliqueDriver.time .suppliedPrivate) := by
  intro w
  apply CliqueDriver.program_executes .suppliedPrivate g w
  intro _ q
  exact hg (CliqueRecovery.query true w q)
    (privateMatrixDiagram (fun i => (sampleWord w.word q.1.val).get i) w.source w.target (2*q.2.val))
    (privateMatrixDiagram_graph _ _ _ _) (privateGraphInput_chordal _ _ _ _)

/-- Hardness persists when the actual finite endpoint representation is supplied
with the graph; the reducer physically emits every endpoint rank. -/
theorem suppliedPrivate_matching_sharpPHard (g : BitString → ℕ) (hg : SuppliedChordalPermutationOracle g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard (CliqueDriver.program .suppliedPrivate) g (CliqueDriver.time .suppliedPrivate)
    (suppliedPrivate_wordSolverSpec g hg)
end HiddenCircuits.GraphReduction
