import HiddenCircuits.GraphReduction.PrivateProbeReduction
import HiddenCircuits.GraphReduction.MonotoneReduction
import HiddenCircuits.GraphReduction.UnitIntervalRecovery
import HiddenCircuits.GraphReduction.UnitIntervalQueryBounds
import HiddenCircuits.PairedInterpolation

/-! Composition of the actual shared paired sampling with the explicit target-graph oracle families. -/
namespace HiddenCircuits.GraphReduction
open scoped BigOperators

/-- Both nested graph constructions use these actual paired samples of the source word. -/
def wordPairSample (w : WordInstance) (t : Fin (w.word.length*w.particles^2+1)) := sampleWord w.word t.val

/-- Empty words are handled by their boundary Kronecker delta, without graph queries. -/
noncomputable def recoverWordViaPairs (w : WordInstance)
    (oracle : List (CutPair w.particles) → State (2*w.particles) w.particles →
      State (2*w.particles) w.particles → ℚ) : ℚ :=
  if w.word=[] then (if w.source=w.target then 1 else 0) else
    (Complexity.interpolateValues (w.word.length*w.particles^2)
      (fun t => oracle (wordPairSample w t) w.source w.target)).eval (-1)

private theorem recoverWordViaPairs_correct (w : WordInstance)
    (oracle : List (CutPair w.particles) → State (2*w.particles) w.particles →
      State (2*w.particles) w.particles → ℚ)
    (horacle : ∀ v, v≠[] → ∀ S T, oracle v S T=pairWordMatrix v S T) :
    recoverWordViaPairs w oracle=w.value := by
  unfold recoverWordViaPairs
  by_cases hw : w.word=[]
  · rw [if_pos hw]
    simp [WordInstance.value,hw,wordMatrix,Matrix.one_apply]
  · rw [if_neg hw]
    have he : (fun t : Fin (w.word.length*w.particles^2+1) => oracle (wordPairSample w t) w.source w.target)=
        (fun t => pairWordMatrix (sampleWord w.word t.val) w.source w.target) := by
      funext t
      exact horacle _ (pairedQuery_nonempty w.word hw t.val) _ _
    rw [he]
    exact recoverWordFromPairs_correct w.word w.source w.target

noncomputable def recoverWordFromMonotone (w : WordInstance) : ℚ :=
  recoverWordViaPairs w recoverPairFromMonotone

noncomputable def recoverWordFromUnitIntervals (w : WordInstance) : ℚ :=
  recoverWordViaPairs w recoverPairFromUnitIntervals

/-- Actual WordEval recovery from actual simple unweighted monotone queries. -/
theorem recoverWordFromMonotone_correct (w : WordInstance) : recoverWordFromMonotone w=w.value :=
  recoverWordViaPairs_correct w _ recoverPairFromMonotone_correct

/-- Actual WordEval recovery from the explicitly represented unit-interval query family. -/
theorem recoverWordFromUnitIntervals_correct (w : WordInstance) : recoverWordFromUnitIntervals w=w.value :=
  recoverWordViaPairs_correct w _ recoverPairFromUnitIntervals_correct

noncomputable def recoverWordFromChordalPermutation (w : WordInstance) : ℚ :=
  recoverWordViaPairs w PrivateProbe.recoverPair

/-- Actual WordEval recovery from the fully represented chordal permutation graphs. -/
theorem recoverWordFromChordalPermutation_correct (w : WordInstance) :
    recoverWordFromChordalPermutation w=w.value :=
  recoverWordViaPairs_correct w _ PrivateProbe.recoverPair_correct

/-- The explicit nested interpolation grid, before the optional empty-word fast path. -/
def WordGraphQueryIndex (w : WordInstance) :=
  Σ t : Fin (w.word.length*w.particles^2+1), Fin (2*w.particles*(wordPairSample w t).length+1)

instance (w : WordInstance) : Fintype (WordGraphQueryIndex w) := by unfold WordGraphQueryIndex; infer_instance

def maxPairedQueryLength (w : WordInstance) : ℕ := w.word.length*(w.word.length*w.particles^2+1)

 theorem wordPairSample_bound (w : WordInstance) (t : Fin (w.word.length*w.particles^2+1)) :
    (wordPairSample w t).length ≤ maxPairedQueryLength w := (pairedQuery_size w.word t).2

/-- The literal nested finite query index has polynomial cardinality in p and the source word length. -/
theorem wordGraphQuery_count (w : WordInstance) :
    Fintype.card (WordGraphQueryIndex w) ≤
      (w.word.length*w.particles^2+1)*(2*w.particles*maxPairedQueryLength w+1) := by
  unfold WordGraphQueryIndex
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ t : Fin (w.word.length*w.particles^2+1), (2*w.particles*(wordPairSample w t).length+1)) ≤
      ∑ _t : Fin (w.word.length*w.particles^2+1), (2*w.particles*maxPairedQueryLength w+1) :=
      Finset.sum_le_sum (fun t _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (wordPairSample_bound w t)) 1)
    _ = _ := by simp [Nat.mul_comm]

/-- Every graph queried in the unit-interval composition has a constructed equal-length representation. -/
def wordUnitIntervalRepresentation (w : WordInstance) (q : WordGraphQueryIndex w) :
    UnitInterval.Representation (unitIntervalQueryGraph
      (fun r => (wordPairSample w q.1).get r) w.source w.target (2*q.2.val)) :=
  unitIntervalQueryRepresentation (wordPairSample w q.1) w.source w.target (2*q.2.val)

/-- Uniform vertex-size bound over the entire actual nested unit-interval query family. -/
theorem wordUnitIntervalQuery_size (w : WordInstance) (hw : w.word≠[]) (q : WordGraphQueryIndex w) :
    Fintype.card (UnitOriginalVertex w.particles (wordPairSample w q.1).length w.source w.target ⊕
      (Fin ((wordPairSample w q.1).length+1) × Fin (2*q.2.val))) ≤
      4*w.particles*maxPairedQueryLength w*(maxPairedQueryLength w+2) := by
  have hp := unitIntervalProbe_query_size (List.length_pos_iff.mpr (pairedQuery_nonempty w.word hw q.1.val))
    w.source w.target q.2
  apply hp.trans
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (wordPairSample_bound w q.1))
    (Nat.add_le_add_right (wordPairSample_bound w q.1) 2)

end HiddenCircuits.GraphReduction
