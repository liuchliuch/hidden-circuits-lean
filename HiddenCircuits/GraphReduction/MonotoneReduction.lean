import HiddenCircuits.GraphReduction.MonotoneQueries
import HiddenCircuits.GraphReduction.MonotoneTargetBridge

/-! The Section 9 graph-oracle identity is connected to the actual paired-transfer input.
All submitted graphs and both ordered representations are explicit constructions. -/
namespace HiddenCircuits.GraphReduction

/-- The explicit Section 9 postprocessing of the monotone graph query counts. -/
noncomputable def recoverPairFromMonotone {p : ℕ} (w : List (CutPair p))
    (S T : State (2*p) p) : ℚ := recoverMonotoneTarget (fun r => w.get r) S T

/-- Exact PairEval recovery from simple unweighted monotone graphs, without an
assumed graph-count identity or a supplied representation certificate. -/
theorem recoverPairFromMonotone_correct {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) : recoverPairFromMonotone w S T = pairWordMatrix w S T := by
  unfold recoverPairFromMonotone
  rw [recoverMonotoneTarget_correct (List.length_pos_iff.mpr hw),retainedTarget_matchingCount]

/-- Each actual submitted query comes with the proved permutation diagram,
constructed monotone ordering, and the paper's polynomial vertex bound. -/
theorem monotonePairQuery_valid {p : ℕ} (w : List (CutPair p)) (hw : w≠[])
    (S T : State (2*p) p) (s : Fin (2*p*w.length+1)) :
    (retainedMonotoneDiagram (fun r => w.get r) S T s.val).graph =
        monotoneQueryGraph (fun r => w.get r) S T s.val ∧
      Nonempty (MonotoneOrdering (probeRelation (retainedQueryRelation (fun r => w.get r) S T)
        (retainedEvenAttachment S T) oddAttachment s.val)) ∧
      Fintype.card (ProbePart (RetainedEven p w.length S T) (Fin w.length) s.val ⊕
        ProbePart (OddVertex (2*p) w.length) (Fin w.length) s.val) ≤ 4*p*w.length*(w.length+1) :=
  monotoneSample_valid (List.length_pos_iff.mpr hw) (fun r => w.get r) S T s

end HiddenCircuits.GraphReduction
