import HiddenCircuits.GraphReduction.Runtime.PairEval.GraphRecovery
import HiddenCircuits.GraphReduction.Runtime.PairEval.CliqueFrontend
import HiddenCircuits.GraphReduction.Runtime.CliqueHardness

/-! Class promises and concrete natural-valued oracle bindings for every
arbitrary canonical PairEval input and each emitted probe node. -/
namespace HiddenCircuits.GraphReduction.Runtime.PairEval.GraphPromises
open Complexity WordGraph GraphRecovery

def OracleSpec (kind : Kind) (g : BitString→ℕ) : Prop :=
  ∀w : PairInput,∀s : Index w,g (query kind w s).encode=perfectMatchingCount (query kind w s).2.graph
lemma monotone_query (w : PairInput) (s : Index w) : MonotoneGraph (query none w s).2.graph :=
  monotoneGraphInput_monotone _ _ _ _
lemma unit_query (w : PairInput) (s : Index w) : UnitIntervalGraph (query (some false) w s).2.graph :=
  unitGraphInput_unit _ _ _ _
lemma private_query (w : PairInput) (s : Index w) : ChordalPermutationGraph (query (some true) w s).2.graph :=
  privateGraphInput_chordalPermutation _ _ _ _
lemma monotone_spec (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>MonotoneGraph G.2.graph) g) :
    OracleSpec none g := fun w s=>hg _ (monotone_query w s)
lemma unit_spec (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>UnitIntervalGraph G.2.graph) g) :
    OracleSpec (some false) g := fun w s=>hg _ (unit_query w s)
lemma private_spec (g : BitString→ℕ) (hg : ClassMatchingOracle (fun G=>ChordalPermutationGraph G.2.graph) g) :
    OracleSpec (some true) g := fun w s=>hg _ (private_query w s)
lemma canonical_spec (kind : Kind) : OracleSpec kind GraphInput.perfectMatchingProblem := by
  intro w s
  simp [GraphInput.perfectMatchingProblem]

lemma monotone_bytes (w : PairInput) (s : Index w) :
    GraphFrontend.queryBits w 0 s.val=(query none w s).encode := rfl
lemma unit_bytes (w : PairInput) (s : Index w) :
    CliqueFrontend.queryBits .unit w 0 s.val=(query (some false) w s).encode := rfl
lemma private_bytes (w : PairInput) (s : Index w) :
    CliqueFrontend.queryBits .privateGraph w 0 s.val=(query (some true) w s).encode := rfl
lemma suppliedPrivate_bytes (w : PairInput) (s : Index w) :
    CliqueFrontend.queryBits .suppliedPrivate w 0 s.val=
      suppliedPermutationBits (query (some true) w s)
        (privateMatrixDiagram (fun i=>w.pairs.get i) w.source w.target (2*s.val)) := rfl
lemma suppliedPrivate_spec (g : BitString→ℕ) (hg : SuppliedChordalPermutationOracle g) (w : PairInput) (s : Index w) :
    g (CliqueFrontend.queryBits .suppliedPrivate w 0 s.val)=perfectMatchingCount (query (some true) w s).2.graph :=
  hg _ _ (privateMatrixDiagram_graph _ _ _ _) (privateGraphInput_chordal _ _ _ _)

/-- A total canonical extension for the supplied-diagram promise problem. The
redundant graph field determines the count; rejected list encodings return zero. -/
noncomputable def suppliedPrivateProblem (xs : BitString) : ℕ :=
  match decodeBitList xs with
  | some (graph::_) => GraphInput.perfectMatchingProblem graph
  | _ => 0
lemma suppliedPrivateProblem_spec : SuppliedChordalPermutationOracle suppliedPrivateProblem := by
  intro G D hD hG
  simp [suppliedPrivateProblem,suppliedPermutationBits,GraphInput.perfectMatchingProblem]
lemma suppliedPrivate_canonical (w : PairInput) (s : Index w) :
    suppliedPrivateProblem (CliqueFrontend.queryBits .suppliedPrivate w 0 s.val)=
      perfectMatchingCount (query (some true) w s).2.graph :=
  suppliedPrivate_spec _ suppliedPrivateProblem_spec w s
end HiddenCircuits.GraphReduction.Runtime.PairEval.GraphPromises
