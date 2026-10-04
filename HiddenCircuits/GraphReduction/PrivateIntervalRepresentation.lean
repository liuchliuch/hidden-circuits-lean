import HiddenCircuits.GraphReduction.PrivateIntervalOrder
import HiddenCircuits.GraphReduction.QueryRepresentations

/-! Actual integer interval coordinates on the emitted numeric query labels. -/
namespace HiddenCircuits.GraphReduction

namespace PrivateProbe
lemma retainedEmbedding_adj {p h s : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p)
    (x y : RetainedOriginal p h S T ⊕ (Layer h × Fin s)) :
    (queryGraph pairs s).Adj (retainedEmbedding S T s x) (retainedEmbedding S T s y) ↔
      (retainedQueryGraph pairs S T s).Adj x y := by
  rcases x with x|x  <;>  rcases y with y|y  <;>  rfl
end PrivateProbe

/-- The numeric label maps to its explicit layered, probe-first right-endpoint key. -/
def privateMatrixIntervalKey {p h : ℕ} (S T : State (2*p) p) (s : ℕ) :
    Fin (privateEnumeration (h:=h) S T s).labels.length ↪ ℕ :=
  ⟨fun i =>  PrivateProbe.intervalKey (PrivateProbe.retainedEmbedding S T s
      ((privateEnumeration (h:=h) S T s).labels.get i)),
    PrivateProbe.intervalKey_injective.comp ((PrivateProbe.retainedEmbedding S T s).injective.comp
      (privateEnumeration (h:=h) S T s).nodup.injective_get)⟩

lemma privateMatrixIntervalKey_suffix {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    Interval.SuffixOrder (privateGraphInput pairs S T s).2.graph (privateMatrixIntervalKey (h:=h) S T s) := by
  intro x y z hxy hyz hxz
  change decide ((PrivateProbe.retainedQueryGraph pairs S T s).Adj _ _) = true at hxz ⊢
  apply decide_eq_true_eq.mpr
  apply (PrivateProbe.retainedEmbedding_adj pairs S T _ _).mp
  apply PrivateProbe.intervalKey_suffix pairs _ _ _ hxy hyz
  exact (PrivateProbe.retainedEmbedding_adj pairs S T _ _).mpr (of_decide_eq_true hxz)

/-- Supplied left and right coordinates are the two literal finite scan counts. -/
def privateMatrixIntervalRepresentation {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    Interval.NatRepresentation (privateGraphInput pairs S T s).2.graph :=
  Interval.ofSuffixOrder (privateMatrixIntervalKey (h:=h) S T s) (privateMatrixIntervalKey_suffix pairs S T s)

/-- The coordinates denote genuine intersecting closed rational intervals. -/
def privateMatrixRationalIntervalRepresentation {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    Interval.Representation (privateGraphInput pairs S T s).2.graph :=
  (privateMatrixIntervalRepresentation pairs S T s).toRational

 theorem privateMatrixIntervalRepresentation_bounds {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) (v : Fin (privateGraphInput pairs S T s).1) :
    (privateMatrixIntervalRepresentation pairs S T s).left v  ≤ 
      (privateMatrixIntervalRepresentation pairs S T s).right v ∧
    (privateMatrixIntervalRepresentation pairs S T s).right v  <  (privateGraphInput pairs S T s).1 := by
  simpa only [Fintype.card_fin] using Interval.ofSuffixOrder_bounds
    (privateMatrixIntervalKey (h:=h) S T s) (privateMatrixIntervalKey_suffix pairs S T s) v

end HiddenCircuits.GraphReduction
