import HiddenCircuits.GraphReduction.PrivateProbeRepresentation
import HiddenCircuits.GraphReduction.PermutationRankCompression
import HiddenCircuits.GraphReduction.MonotoneSize

/-! Boundary restriction, literal query sizes, and endpoint coordinates bounded by the actual vertex count. -/
namespace HiddenCircuits.GraphReduction.PrivateProbe
open scoped BigOperators

/-- Delete only the unwanted boundary original vertices from both endpoint orders. -/
def retainedDiagram {p h : ℕ} (pairs : Fin h → CutPair p) (S T : State (2*p) p) (s : ℕ) :=
  (diagram pairs s).restrict (retainedEmbedding S T s)

 theorem retainedDiagram_graph {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    (retainedDiagram pairs S T s).graph=retainedQueryGraph pairs S T s := by
  ext x y
  change (diagram pairs s).graph.Adj (retainedEmbedding S T s x) (retainedEmbedding S T s y) ↔ _
  rw [diagram_graph]
  rcases x with x|⟨i,q⟩ <;> rcases y with y|⟨j,t⟩
  · rfl
  · rfl
  · rfl
  · rfl

 theorem retainedOriginal_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) :
    Fintype.card (RetainedOriginal p h S T)=4*p*h := by
  rw [Fintype.card_sum,retainedEven_card hh,oddVertex_card]
  ring

 theorem layer_card (h : ℕ) : Fintype.card (Layer h)=2*h+1 := by
  simp [Layer]
  omega

/-- The actual Section11 query has precisely 4ph+(2h+1)s vertices. -/
theorem retainedQuery_card {p h : ℕ} (hh : 0<h) (S T : State (2*p) p) (s : ℕ) :
    Fintype.card (RetainedOriginal p h S T ⊕ (Layer h × Fin s))=4*p*h+(2*h+1)*s := by
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,retainedOriginal_card hh,layer_card]

/-- Endpoint coordinates are the actual order ranks after boundary deletion. -/
noncomputable def boundedDiagram {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) := (retainedDiagram pairs S T s).compress

@[simp] theorem boundedDiagram_graph {p h : ℕ} (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) :
    (boundedDiagram pairs S T s).graph=retainedQueryGraph pairs S T s := by
  rw [boundedDiagram,PermutationDiagram.compress_graph,retainedDiagram_graph]

 theorem boundedDiagram_upper_lt {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) (v) :
    (boundedDiagram pairs S T s).upper v<4*p*h+(2*h+1)*s := by
  rw [← retainedQuery_card hh S T s]
  exact (retainedDiagram pairs S T s).compress_upper_lt v

 theorem boundedDiagram_lower_lt {p h : ℕ} (hh : 0<h) (pairs : Fin h → CutPair p)
    (S T : State (2*p) p) (s : ℕ) (v) :
    (boundedDiagram pairs S T s).lower v<4*p*h+(2*h+1)*s := by
  rw [← retainedQuery_card hh S T s]
  exact (retainedDiagram pairs S T s).compress_lower_lt v

/-- Each interpolation query is simple, unweighted, and has the stated quadratic-in-h size bound. -/
theorem sampleQuery_size_bound {p h : ℕ} (hh : 0<h) (S T : State (2*p) p)
    (t : Fin (2*p*h+1)) :
    Fintype.card (RetainedOriginal p h S T ⊕ (Layer h × Fin (2*t.val))) ≤ 8*p*h*(h+1) := by
  rw [retainedQuery_card hh]
  have ht := t.isLt
  have ht' : 2*t.val≤4*p*h := by nlinarith
  have hm := Nat.mul_le_mul_left (2*h+1) ht'
  nlinarith

end HiddenCircuits.GraphReduction.PrivateProbe
