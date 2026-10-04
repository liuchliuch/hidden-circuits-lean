import HiddenCircuits.GraphReduction.PrivateProbeQueries
import HiddenCircuits.GraphReduction.PrivateProbeChordal
import HiddenCircuits.GraphReduction.PrivateProbeRecovery

/-! One concrete Section11 endpoint: actual query graphs, supplied endpoint ranks,
actual chordality, exact sizes, and exact recovery of the paired-transfer entry. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe

/-- Every submitted even-size query has the proved endpoint representation, actual
chordality and paper vertex bound, with endpoint ranks below its exact size. -/
theorem pairQuery_valid {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) (t : Fin (2*p*w.length+1)) :
    let pairs := fun r => w.get r
    let s := 2*t.val
    (boundedDiagram pairs S T s).graph=retainedQueryGraph pairs S T s ∧
      Chordal (retainedQueryGraph pairs S T s) ∧
      Nonempty (PerfectEliminationOrder (retainedQueryGraph pairs S T s)) ∧
      Fintype.card (RetainedOriginal p w.length S T ⊕ (Layer w.length × Fin s)) =
        4*p*w.length+(2*w.length+1)*s ∧
      Fintype.card (RetainedOriginal p w.length S T ⊕ (Layer w.length × Fin s)) ≤
        8*p*w.length*(w.length+1) ∧
      (∀ v, (boundedDiagram pairs S T s).upper v<4*p*w.length+(2*w.length+1)*s ∧
        (boundedDiagram pairs S T s).lower v<4*p*w.length+(2*w.length+1)*s) := by
  have hh := List.length_pos_iff.mpr hw
  exact ⟨boundedDiagram_graph _ S T _,retainedQueryGraph_chordal _ S T _,
    ⟨retainedQueryOrder _ S T _⟩,retainedQuery_card hh S T _,sampleQuery_size_bound hh S T t,
    fun v => ⟨boundedDiagram_upper_lt hh _ S T _ v,boundedDiagram_lower_lt hh _ S T _ v⟩⟩

/-- Exact PairEval recovery together with the actual supplied representation,
chordality and bounded vertex/rank data for every query used by that recovery. -/
theorem pairEval_from_chordalPermutationQueries {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) :
    recoverPair w S T=pairWordMatrix w S T ∧
      ∀ t : Fin (2*p*w.length+1),
        let pairs := fun r => w.get r
        let s := 2*t.val
        (boundedDiagram pairs S T s).graph=retainedQueryGraph pairs S T s ∧
          Chordal (retainedQueryGraph pairs S T s) ∧
          Fintype.card (RetainedOriginal p w.length S T ⊕ (Layer w.length × Fin s)) ≤
            8*p*w.length*(w.length+1) ∧
          (∀ v, (boundedDiagram pairs S T s).upper v<4*p*w.length+(2*w.length+1)*s ∧
            (boundedDiagram pairs S T s).lower v<4*p*w.length+(2*w.length+1)*s) := by
  refine ⟨recoverPair_correct w hw S T,?_⟩
  intro t
  have h := pairQuery_valid w hw S T t
  exact ⟨h.1,h.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

end HiddenCircuits.GraphReduction.PrivateProbe
