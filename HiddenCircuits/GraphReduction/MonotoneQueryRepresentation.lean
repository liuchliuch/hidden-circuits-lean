import HiddenCircuits.GraphReduction.MonotoneRepresentation

/-! Boundary deletion and the actual monotone ordering of every Section 9 query graph. -/
namespace HiddenCircuits.GraphReduction

/-- Restrict a genuine endpoint diagram to any explicitly included vertex set. -/
def PermutationDiagram.restrict {V W : Type*} (D : PermutationDiagram V) (e : W ↪ V) :
    PermutationDiagram W where
  upper := e.trans D.upper
  lower := e.trans D.lower

/-- The actual endpoint diagram after the required first/last boundary deletions. -/
def retainedMonotoneDiagram {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    PermutationDiagram
      (ProbePart (RetainedEven p h S T) (Fin h) s ⊕ ProbePart (OddVertex (2*p) h) (Fin h) s) :=
  (fullMonotoneDiagram pairs s).restrict (retainedVertexEmbedding S T s)

/-- Lemma 9.2's representation assertion, for the literal retained probe graph. -/
theorem retainedMonotoneDiagram_graph {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    (retainedMonotoneDiagram pairs S T s).graph = monotoneQueryGraph pairs S T s := by
  ext v w
  change (fullMonotoneDiagram pairs s).graph.Adj
      (retainedVertexEmbedding S T s v) (retainedVertexEmbedding S T s w) ↔ _
  rw [fullMonotoneDiagram_graph]
  rcases v with ((a | q) | (b | t)) <;> rcases w with ((a' | q') | (b' | t')) <;> rfl

/-- An explicit, genuine monotone ordering of the actual query relation. -/
noncomputable def monotoneQueryOrdering {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    MonotoneOrdering (probeRelation (retainedQueryRelation pairs S T)
      (retainedEvenAttachment S T) oddAttachment s) := by
  have hX : ∀ x y, ¬(retainedMonotoneDiagram pairs S T s).graph.Adj (.inl x) (.inl y) := by
    intro x y
    rw [retainedMonotoneDiagram_graph]
    exact fun h => h
  have hY : ∀ x y, ¬(retainedMonotoneDiagram pairs S T s).graph.Adj (.inr x) (.inr y) := by
    intro x y
    rw [retainedMonotoneDiagram_graph]
    exact fun h => h
  change MonotoneOrdering (fun x y => (monotoneQueryGraph pairs S T s).Adj (.inl x) (.inr y))
  rw [← retainedMonotoneDiagram_graph]
  exact (retainedMonotoneDiagram pairs S T s).monotoneOrdering hX hY

 theorem digitRank_bound {B L : ℕ} (x : Fin B × Fin L) : digitRank x < B*L := by
  have hb := Nat.mul_le_mul_right L (Nat.succ_le_iff.mpr x.1.isLt)
  have ho := x.2.isLt
  unfold digitRank
  nlinarith

/-- Both explicit endpoint coordinates have a polynomial numerical bound. -/
theorem fullMonotoneDiagram_rank_bound {p h : ℕ} (pairs : Fin h → CutPair p) (s : ℕ)
    (v : MonotoneVertex (2*p) h s) :
    (fullMonotoneDiagram pairs s).upper v < (h+1)*(4*p+2*s) ∧
      (fullMonotoneDiagram pairs s).lower v < (h+1)*(4*p+2*s) := by
  have hu := digitRank_bound (upperPosition pairs v)
  have hl := digitRank_bound (lowerPosition pairs v)
  have hw : endpointBlockWidth (2*p) s = 4*p+2*s := by unfold endpointBlockWidth; omega
  exact ⟨hu.trans_eq (congrArg (fun L => (h+1)*L) hw),
    hl.trans_eq (congrArg (fun L => (h+1)*L) hw)⟩

 theorem retainedMonotoneDiagram_rank_bound {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ)
    (v : ProbePart (RetainedEven p h S T) (Fin h) s ⊕ ProbePart (OddVertex (2*p) h) (Fin h) s) :
    (retainedMonotoneDiagram pairs S T s).upper v < (h+1)*(4*p+2*s) ∧
      (retainedMonotoneDiagram pairs S T s).lower v < (h+1)*(4*p+2*s) :=
  fullMonotoneDiagram_rank_bound pairs s (retainedVertexEmbedding S T s v)

end HiddenCircuits.GraphReduction
