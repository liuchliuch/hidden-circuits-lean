import HiddenCircuits.GraphReduction.Runtime.SuppliedMembershipProjection
import HiddenCircuits.GraphReduction.Runtime.SuppliedUnitHardness
import HiddenCircuits.GraphReduction.Runtime.PrivateBothHardness

/-! Explicit #P-complete extensions of the three supplied-representation promises.

These total functions count perfect matchings in the explicit graph field. They
check the framing of the projected field(s), then run the ordinary graph decoder.
They intentionally do not validate the representation bytes, their agreement
with the graph, graph-class membership, the packet's remaining list framing, or
its number of fields. On the original well-formed promises, the supplied graph
field is exact and each original hardness theorem applies. No theorem here
asserts membership for every arbitrary promise extension, or changes the older
whole-list-decoding `PairEval.GraphPromises.suppliedPrivateProblem`. -/
namespace HiddenCircuits.GraphReduction
open Complexity Runtime.SuppliedMembership

/-- Graph-field projection extension for the supplied unit-interval promise.
The representation is not validated on inputs outside that promise. -/
noncomputable def suppliedUnitGraphFieldProblem : BitString→ℕ :=
  GraphInput.perfectMatchingProblem ∘ graphField

/-- Graph-field projection extension for the supplied chordal-permutation
promise. This is not a whole-packet or representation validation function. -/
noncomputable def suppliedPrivateGraphFieldProblem : BitString→ℕ :=
  GraphInput.perfectMatchingProblem ∘ graphField

/-- Twice-projected graph-field extension for the jointly supplied interval and
permutation promise. The two representation payloads are not validated. -/
noncomputable def suppliedBothGraphFieldProblem : BitString→ℕ :=
  GraphInput.perfectMatchingProblem ∘ nestedGraphField

lemma suppliedUnit_graphField (G : GraphInput) (R : UnitIntegerRepresentation G) :
    graphField (suppliedUnitBits G R)=G.encode := by
  exact graphField_cons _ _
lemma suppliedPrivate_graphField (G : GraphInput) (D : PermutationDiagram (Fin G.1)) :
    graphField (suppliedPermutationBits G D)=G.encode := by
  exact graphField_cons _ _
lemma suppliedBoth_graphField (G : GraphInput) (D : PermutationDiagram (Fin G.1))
    (I : Interval.NatRepresentation G.2.graph) :
    nestedGraphField (suppliedIntervalPermutationBits G D I)=G.encode := by
  simp only [nestedGraphField,suppliedIntervalPermutationBits,graphField_cons]

theorem suppliedUnitGraphFieldProblem_oracle : SuppliedUnitOracle suppliedUnitGraphFieldProblem := by
  intro G R
  simp only [suppliedUnitGraphFieldProblem,Function.comp_apply,suppliedUnit_graphField,
    GraphInput.perfectMatchingProblem,GraphInput.decode_encode]
theorem suppliedPrivateGraphFieldProblem_oracle :
    SuppliedChordalPermutationOracle suppliedPrivateGraphFieldProblem := by
  intro G D _ _
  simp only [suppliedPrivateGraphFieldProblem,Function.comp_apply,suppliedPrivate_graphField,
    GraphInput.perfectMatchingProblem,GraphInput.decode_encode]
theorem suppliedBothGraphFieldProblem_oracle :
    SuppliedIntervalPermutationOracle suppliedBothGraphFieldProblem := by
  intro G D I _
  simp only [suppliedBothGraphFieldProblem,Function.comp_apply,suppliedBoth_graphField,
    GraphInput.perfectMatchingProblem,GraphInput.decode_encode]

theorem suppliedUnitGraphFieldProblem_sharpP : SharpP suppliedUnitGraphFieldProblem :=
  GraphVerifier.MatchingPullback.sharpP_of_graph_compiler program program_queryFree
    graphField time size (program_executes (fun _=>0)) size_bound

theorem suppliedPrivateGraphFieldProblem_sharpP : SharpP suppliedPrivateGraphFieldProblem :=
  suppliedUnitGraphFieldProblem_sharpP

theorem suppliedBothGraphFieldProblem_sharpP : SharpP suppliedBothGraphFieldProblem :=
  GraphVerifier.MatchingPullback.sharpP_of_graph_compiler nestedProgram nestedProgram_queryFree
    nestedGraphField nestedTime size (nestedProgram_executes (fun _=>0)) nestedSize_bound

theorem suppliedUnitGraphFieldProblem_sharpPHard : SharpPHard suppliedUnitGraphFieldProblem :=
  suppliedUnit_matching_sharpPHard _ suppliedUnitGraphFieldProblem_oracle

theorem suppliedPrivateGraphFieldProblem_sharpPHard : SharpPHard suppliedPrivateGraphFieldProblem :=
  suppliedPrivate_matching_sharpPHard _ suppliedPrivateGraphFieldProblem_oracle

theorem suppliedBothGraphFieldProblem_sharpPHard : SharpPHard suppliedBothGraphFieldProblem :=
  suppliedBoth_matching_sharpPHard _ suppliedBothGraphFieldProblem_oracle

/-- The supplied unit-interval promise has an explicit machine-grounded
#P-complete extension, without a compiler or polynomiality hypothesis. -/
theorem suppliedUnit_has_sharpP_complete_extension :
    ∃f : BitString→ℕ,SharpP f ∧ SharpPHard f ∧ SuppliedUnitOracle f :=
  ⟨suppliedUnitGraphFieldProblem,suppliedUnitGraphFieldProblem_sharpP,
    suppliedUnitGraphFieldProblem_sharpPHard,suppliedUnitGraphFieldProblem_oracle⟩

/-- The supplied chordal-permutation promise has an explicit machine-grounded
#P-complete extension, without a compiler or polynomiality hypothesis. -/
theorem suppliedPrivate_has_sharpP_complete_extension :
    ∃f : BitString→ℕ,SharpP f ∧ SharpPHard f ∧ SuppliedChordalPermutationOracle f :=
  ⟨suppliedPrivateGraphFieldProblem,suppliedPrivateGraphFieldProblem_sharpP,
    suppliedPrivateGraphFieldProblem_sharpPHard,suppliedPrivateGraphFieldProblem_oracle⟩

/-- The jointly supplied interval and permutation promise has an explicit
machine-grounded #P-complete extension, without a compiler or polynomiality
hypothesis. Membership is for the graph-field projection extension. -/
theorem suppliedBoth_has_sharpP_complete_extension :
    ∃f : BitString→ℕ,SharpP f ∧ SharpPHard f ∧ SuppliedIntervalPermutationOracle f :=
  ⟨suppliedBothGraphFieldProblem,suppliedBothGraphFieldProblem_sharpP,
    suppliedBothGraphFieldProblem_sharpPHard,suppliedBothGraphFieldProblem_oracle⟩

end HiddenCircuits.GraphReduction
