import HiddenCircuits.GraphReduction.ProbeDecidable
import HiddenCircuits.GraphReduction.UnitIntervalGraphs
import HiddenCircuits.GraphReduction.PrivateProbeVertices

/-! Literal decidable adjacency for the unweighted clique-probe query families. -/
namespace HiddenCircuits.GraphReduction
variable {V I : Type*}

instance decidableCliqueProbeGraph (G : SimpleGraph V) (A : I → V → Prop)
    [DecidableEq I] [DecidableRel G.Adj] [∀ i, DecidablePred (A i)] (s : ℕ) :
    DecidableRel (cliqueProbeGraph G A s).Adj := by
  intro v w
  cases v with
  | inl v => cases w <;> dsimp [cliqueProbeGraph] <;> infer_instance
  | inr v => cases w <;> dsimp [cliqueProbeGraph] <;> infer_instance

instance decidableUnitIntervalCross {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    DecidableRel (unitIntervalCrossRelation pairs S T) := by
  intro v w
  unfold unitIntervalCrossRelation
  infer_instance

instance decidableUnitIntervalOriginal {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    DecidableRel (unitIntervalOriginalGraph pairs S T).Adj := by
  intro v w
  cases v <;> cases w <;> dsimp [unitIntervalOriginalGraph] <;> infer_instance

instance decidableUnitIntervalAttachment {p h : ℕ} (S T : State (2*p) p) (r : Fin (h+1)) :
    DecidablePred (unitIntervalAttachment S T r) := by
  intro v
  cases v <;> dsimp [unitIntervalAttachment] <;> infer_instance

instance decidableUnitIntervalQuery {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    DecidableRel (unitIntervalQueryGraph pairs S T s).Adj := decidableCliqueProbeGraph _ _ s

namespace PrivateProbe
instance decidableCliqueGraph {p h : ℕ} (pairs : Fin h → CutPair p) : DecidableRel (cliqueGraph pairs).Adj := by
  intro v w
  rcases v with ⟨j,u⟩|⟨r,u⟩ <;> rcases w with ⟨k,v⟩|⟨t,v⟩ <;> dsimp [cliqueGraph] <;> infer_instance

instance decidableRetainedCliqueGraph {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) :
    DecidableRel (retainedCliqueGraph pairs S T).Adj :=
  fun v w => decidableCliqueGraph pairs (originalEmbedding S T v) (originalEmbedding S T w)

instance decidableRetainedQueryGraph {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :
    DecidableRel (retainedQueryGraph pairs S T s).Adj := decidableCliqueProbeGraph _ _ s
end PrivateProbe

end HiddenCircuits.GraphReduction
