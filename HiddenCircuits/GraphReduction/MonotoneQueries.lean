import HiddenCircuits.GraphReduction.MonotoneRecovery
import HiddenCircuits.GraphReduction.MonotoneQueryRepresentation
import HiddenCircuits.GraphReduction.MonotoneMatchingSign
import HiddenCircuits.GraphReduction.ProbeDecidable
import HiddenCircuits.GraphReduction.ProbeFactor

/-! The actual Section 9 query family carries verified permutation and monotone representations. -/
namespace HiddenCircuits.GraphReduction

/-- The sampled diagrams use polynomially bounded integer coordinates on both lines. -/
theorem monotoneSample_rank_bound {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : Fin (2*p*h+1))
    (v : ProbePart (RetainedEven p h S T) (Fin h) s.val ⊕
      ProbePart (OddVertex (2*p) h) (Fin h) s.val) :
    (retainedMonotoneDiagram pairs S T s.val).upper v < 4*p*(h+1)^2 ∧
      (retainedMonotoneDiagram pairs S T s.val).lower v < 4*p*(h+1)^2 := by
  have hv := retainedMonotoneDiagram_rank_bound pairs S T s.val v
  have hs : s.val≤2*p*h := by omega
  have hb : (h+1)*(4*p+2*s.val) ≤ 4*p*(h+1)^2 := by
    calc
      (h+1)*(4*p+2*s.val) ≤ (h+1)*(4*p+2*(2*p*h)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hs) _)
      _ = _ := by ring
  exact ⟨hv.1.trans_le hb,hv.2.trans_le hb⟩

/-- Every oracle query in the recovery is genuinely monotone and has the stated size.
Both representations are constructed from the literal graph, with no representation hypothesis. -/
theorem monotoneSample_valid {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : Fin (2*p*h+1)) :
    (retainedMonotoneDiagram pairs S T s.val).graph = monotoneQueryGraph pairs S T s.val ∧
      Nonempty (MonotoneOrdering (probeRelation (retainedQueryRelation pairs S T)
        (retainedEvenAttachment S T) oddAttachment s.val)) ∧
      Fintype.card (ProbePart (RetainedEven p h S T) (Fin h) s.val ⊕
        ProbePart (OddVertex (2*p) h) (Fin h) s.val) ≤ 4*p*h*(h+1) :=
  ⟨retainedMonotoneDiagram_graph pairs S T s.val,
    ⟨monotoneQueryOrdering pairs S T s.val⟩,monotoneProbe_query_size hh S T s⟩

end HiddenCircuits.GraphReduction
