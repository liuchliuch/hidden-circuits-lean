import HiddenCircuits.Circuit.Runtime.SourceHardness
import HiddenCircuits.GraphReduction.Runtime.WordGraph.WordSolver
import HiddenCircuits.Complexity.GraphVerifier.MatchingFinalRuntime

/-! Machine-grounded #P-completeness on ordinary monotone graph inputs.
A graph-class restriction is expressed in the standard promise form: it has a
#P extension, and every oracle agreeing on promised inputs is #P-hard. There is
no graph recognizer supplied as an assumption and no query-family surrogate for
the natural graph class. -/
namespace HiddenCircuits.GraphReduction
open Complexity

/-- A bipartite graph with an ordering whose row-neighborhood endpoints are
both nondecreasing. The isomorphism makes the predicate independent of labels. -/
def MonotoneGraph {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y) (R : X → Y → Prop),
    Nonempty (MonotoneOrdering R) ∧ Nonempty (G ≃g cutGraph R)

def ClassMatchingOracle (P : GraphInput → Prop) (g : BitString → ℕ) : Prop :=
  ∀G : GraphInput, P G → g G.encode=perfectMatchingCount G.2.graph

def ClassMatchingSharpPComplete (P : GraphInput → Prop) : Prop :=
  (∃ f : BitString → ℕ, SharpP f ∧ ClassMatchingOracle P f) ∧
    ∀ g : BitString → ℕ, ClassMatchingOracle P g → SharpPHard g

lemma classMatchingOracle_full (P : GraphInput → Prop) : ClassMatchingOracle P GraphInput.perfectMatchingProblem := by
  intro G _
  simp [GraphInput.perfectMatchingProblem]

lemma monotoneGraphInput_monotone {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) : MonotoneGraph (monotoneGraphInput pairs S T s).2.graph := by
  refine ⟨ProbePart (RetainedEven p h S T) (Fin h) s,ProbePart (OddVertex (2*p) h) (Fin h) s,
    inferInstance,inferInstance,_,⟨monotoneQueryOrdering pairs S T s⟩,?_⟩
  exact ⟨(monotoneEnumeration S T s).graphIso (monotoneQueryGraph pairs S T s)⟩

lemma monotone_wordSolverSpec (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => MonotoneGraph G.2.graph) g) :
    Circuit.Runtime.SourceWordCall.WordSolverSpec Runtime.WordGraph.Driver.program g Runtime.WordGraph.Driver.time := by
  intro w
  apply Runtime.WordGraph.Driver.program_executes g w
  intro _ q
  exact hg (Runtime.WordGraph.Recovery.query w q) (monotoneGraphInput_monotone _ _ _ _)

/-- Every exact monotone-graph matching oracle is #P-hard under an actual finite
polynomial-bit-time Turing reduction, including the original #P foundation. -/
theorem monotone_matching_sharpPHard (g : BitString → ℕ)
    (hg : ClassMatchingOracle (fun G => MonotoneGraph G.2.graph) g) : SharpPHard g :=
  Circuit.Runtime.SourceReduction.sharpPHard Runtime.WordGraph.Driver.program g Runtime.WordGraph.Driver.time
    (monotone_wordSolverSpec g hg)

/-- Ordinary graph-input #P completeness restricted to the natural monotone
class, with no recognition, runtime, coefficient, or source-hardness premises. -/
theorem monotone_matching_sharpPComplete : ClassMatchingSharpPComplete (fun G => MonotoneGraph G.2.graph) :=
  ⟨⟨GraphInput.perfectMatchingProblem,GraphVerifier.MatchingRuntime.perfectMatching_sharpP,classMatchingOracle_full _⟩,
    monotone_matching_sharpPHard⟩
end HiddenCircuits.GraphReduction
