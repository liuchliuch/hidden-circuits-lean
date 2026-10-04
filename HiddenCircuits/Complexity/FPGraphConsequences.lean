import HiddenCircuits.Complexity.FPCollapse
import HiddenCircuits.GraphReduction.Runtime.MonotoneEndpointHardness
import HiddenCircuits.GraphReduction.RealUnitIntervalsHardness
import HiddenCircuits.GraphReduction.ChordalPermutationInterval
import HiddenCircuits.GraphReduction.Runtime.PrivateBothHardness
import HiddenCircuits.GraphReduction.Runtime.SuppliedUnitHardness

/-! The paper's explicit deterministic exact-counting consequences (TeX
456–457, 659–661, and 728–731): an FP exact oracle on any of the three hard
graph classes would imply literal FP = #P. These are consequences about exact
algorithms; they make no approximation-hardness claim. -/
namespace HiddenCircuits.GraphReduction
open Complexity

/-- Every FP oracle agreeing on a hard graph-class promise yields the collapse,
regardless of its behavior outside that promise. -/
theorem ClassMatchingSharpPComplete.fp_collapse {P : GraphInput → Prop}
    (h : ClassMatchingSharpPComplete P) {g : BitString → ℕ}
    (hg : ClassMatchingOracle P g) (hfp : FP g) : FP_eq_SharpP :=
  (h.2 g hg).fp_eq_sharpP hfp

/-- The graph-class promise admits an FP exact oracle iff FP = #P. The reverse
direction uses the already proved #P extension, with no graph recognizer. -/
theorem ClassMatchingSharpPComplete.fp_oracle_iff_collapse {P : GraphInput → Prop}
    (h : ClassMatchingSharpPComplete P) :
    (∃ g : BitString → ℕ,FP g ∧ ClassMatchingOracle P g) ↔ FP_eq_SharpP := by
  constructor
  · rintro ⟨g,hfp,hg⟩;exact h.fp_collapse hg hfp
  · intro he
    obtain ⟨g,hg,ho⟩ := h.1
    exact ⟨g,(he g).mpr hg,ho⟩

/-- FP ≠ #P excludes every polynomial-time exact oracle on a complete graph
class, without imposing behavior on inputs outside the graph-class promise. -/
theorem ClassMatchingSharpPComplete.no_fp_oracle {P : GraphInput → Prop}
    (h : ClassMatchingSharpPComplete P) (hsep : ¬FP_eq_SharpP) :
    ¬∃ g : BitString → ℕ,FP g ∧ ClassMatchingOracle P g :=
  fun hg => hsep (h.fp_oracle_iff_collapse.mp hg)

/-- Native nondecreasing endpoint arrays, equivalently admissible monotone
restricted permutations: a polynomial-time exact counter implies FP = #P. -/
theorem monotoneEndpoint_fp_collapse (h : FP MonotoneEndpointEncoding.count) : FP_eq_SharpP :=
  monotoneEndpoint_count_sharpPHard.fp_eq_sharpP h

theorem monotoneEndpoint_fp_iff_collapse : FP MonotoneEndpointEncoding.count ↔ FP_eq_SharpP :=
  SharpPComplete.fp_iff_collapse ⟨monotoneEndpoint_count_sharpP,monotoneEndpoint_count_sharpPHard⟩

theorem monotone_matching_fp_collapse {g : BitString → ℕ}
    (hg : ClassMatchingOracle (fun G => MonotoneGraph G.2.graph) g) (hfp : FP g) : FP_eq_SharpP :=
  monotone_matching_sharpPComplete.fp_collapse hg hfp

theorem unit_matching_fp_collapse {g : BitString → ℕ}
    (hg : ClassMatchingOracle (fun G => UnitIntervalGraph G.2.graph) g) (hfp : FP g) : FP_eq_SharpP :=
  unit_matching_sharpPComplete.fp_collapse hg hfp

/-- The natural semantic class with arbitrary real unit-interval endpoints. -/
theorem realUnit_matching_fp_collapse {g : BitString → ℕ}
    (hg : ClassMatchingOracle (fun G => RealUnitInterval.UnitIntervalGraph G.2.graph) g)
    (hfp : FP g) : FP_eq_SharpP :=
  realUnit_matching_sharpPComplete.fp_collapse hg hfp

theorem chordalPermutation_matching_fp_collapse {g : BitString → ℕ}
    (hg : ClassMatchingOracle (fun G => ChordalPermutationGraph G.2.graph) g)
    (hfp : FP g) : FP_eq_SharpP :=
  private_matching_sharpPComplete.fp_collapse hg hfp

/-- Counting remains intractable unless FP = #P on the actual intersection of
interval and permutation graphs. -/
theorem intervalPermutation_matching_fp_collapse {g : BitString → ℕ}
    (hg : ClassMatchingOracle (fun G => IntervalPermutationGraph G.2.graph) g)
    (hfp : FP g) : FP_eq_SharpP :=
  intervalPermutation_matching_sharpPComplete.fp_collapse hg hfp

theorem realIntervalPermutation_matching_fp_collapse {g : BitString → ℕ}
    (hg : ClassMatchingOracle (fun G => RealIntervalPermutationGraph G.2.graph) g)
    (hfp : FP g) : FP_eq_SharpP :=
  realIntervalPermutation_matching_sharpPComplete.fp_collapse hg hfp

/-- Supplying both ordered descriptions does not avoid the collapse. -/
theorem suppliedBoth_matching_fp_collapse {g : BitString → ℕ}
    (hg : SuppliedIntervalPermutationOracle g) (hfp : FP g) : FP_eq_SharpP :=
  (suppliedBoth_matching_sharpPHard g hg).fp_eq_sharpP hfp

theorem suppliedUnit_matching_fp_collapse {g : BitString → ℕ}
    (hg : SuppliedUnitOracle g) (hfp : FP g) : FP_eq_SharpP :=
  (suppliedUnit_matching_sharpPHard g hg).fp_eq_sharpP hfp

/-- The three hard graph classes admit no FP exact oracle if FP ≠ #P. This
statement makes no assertion against efficient approximate oracles/samplers. -/
theorem three_classes_no_fp_exact_oracle (hsep : ¬FP_eq_SharpP) :
    (¬∃ g : BitString → ℕ,FP g ∧ ClassMatchingOracle (fun G => MonotoneGraph G.2.graph) g) ∧
    (¬∃ g : BitString → ℕ,FP g ∧ ClassMatchingOracle
      (fun G => RealUnitInterval.UnitIntervalGraph G.2.graph) g) ∧
    (¬∃ g : BitString → ℕ,FP g ∧ ClassMatchingOracle
      (fun G => RealIntervalPermutationGraph G.2.graph) g) :=
  ⟨monotone_matching_sharpPComplete.no_fp_oracle hsep,
    realUnit_matching_sharpPComplete.no_fp_oracle hsep,
    realIntervalPermutation_matching_sharpPComplete.no_fp_oracle hsep⟩

/-- The supplied-both version of the same conditional impossibility. -/
theorem suppliedBoth_no_fp_exact_oracle (hsep : ¬FP_eq_SharpP) :
    ¬∃ g : BitString → ℕ,FP g ∧ SuppliedIntervalPermutationOracle g := by
  rintro ⟨g,hfp,hg⟩
  exact hsep (suppliedBoth_matching_fp_collapse hg hfp)

end HiddenCircuits.GraphReduction
